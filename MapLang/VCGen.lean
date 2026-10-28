import Lean
import MapLang.While

/-!
# VC-generation tactics for MapLang

A port of `Incorrectness/VCGen.lean` to the map language.  The tactic
*names* are the same (`incorrectness_auto`, `incorrectness_auto_inv`,
`incorrectness_auto_inv_split N inv`, `il_close`, …) but they are
`scoped` to the `MapLang` namespace, so `open MapLang` selects this layer.

What changed with respect to the old layer:

* The state is no longer unfolded into `if`-cascades.  Instead the
  read-after-write lemmas of `MapLang.Core` (`update_same`, `update_ne_ty`,
  `update_ne_name`, `mapUpd_same`, …) are `@[simp]`; their side conditions
  (`"curr" ≠ "prev"`, `.ref ≠ .map .ref .nat`) are discharged by `simp`
  itself (string-literal and constructor simprocs; `decideVarNameEq` decides
  `curr.name = prev.name` for declared variables).  No global `decide := true`
  is needed any more; `decide` is only tried at leaves (`il_leaf`) for closed
  bounded existentials such as `∃ i, i ≤ 2 ∧ …`.
* The `sp` rewriting uses the *first-order* elimination forms `sp_assign`,
  `sp_mapUpdate`, `sp_alloc`, `sp_setInsert`/`sp_setRemove` and
  `sp_relInsert`/`sp_relRemove` — each introduces existentials over old slot
  values / indices / pairs / bits only (never over a function).
* Existentials are eliminated inside `simp` by the simproc `existsPin`,
  which finds a conjunct `v = c` / `c = v` anywhere in the body of `∃ v, …`
  (below `∧` and inner `∃`, also inside disjunctions and hypotheses) and
  substitutes `c`.  The goal-level meta-tactic `il_pin` (same search, but
  only on the goal's outermost `∃`) and the AC-normalising fallback are kept
  as last resorts.
* Loops anywhere in a program (not only at the top) are handled by bounded
  unrolling through `unrollAll` / `vc_unroll_sound`, so a program such as
  "scan loop; splice" is closed by one `incorrectness_auto` call without a
  hand-written midpoint.
* `omega` only recognises `Nat`, so `il_arith` first unfolds the
  `Ty.denote .nat` type annotations produced by typed reads.
-/

open Lean Meta Elab Tactic

namespace MapLang

-- ============================================================
-- Nat-existential helpers (`x := x + k` patterns)
-- ============================================================

theorem exists_and_eq_add {p : Nat → Prop} {n k : Nat} :
    (∃ v, p v ∧ n = v + k) ↔ n ≥ k ∧ p (n - k) := by
  constructor
  · rintro ⟨v, hp, heq⟩
    exact ⟨by omega, by rwa [show n - k = v from by omega]⟩
  · rintro ⟨hge, hp⟩
    exact ⟨n - k, hp, by omega⟩

theorem exists_and_add_eq {p : Nat → Prop} {n k : Nat} :
    (∃ v, p v ∧ v + k = n) ↔ n ≥ k ∧ p (n - k) := by
  constructor
  · rintro ⟨v, hp, heq⟩
    exact ⟨by omega, by rwa [show n - k = v from by omega]⟩
  · rintro ⟨hge, hp⟩
    exact ⟨n - k, hp, by omega⟩

-- ============================================================
-- `existsPin`: witness elimination inside `simp`
-- ============================================================

theorem exists_pin_eq {α : Sort u} (p : α → Prop) (c : α) (h : ∀ v, p v → v = c) :
    (∃ v, p v) = p c :=
  propext ⟨fun ⟨v, hv⟩ => h v hv ▸ hv, fun hc => ⟨c, hc⟩⟩

/-- Given `h : e`, search `e` (through `∧` and inner `∃`) for a conjunct
    `v = c` or `c = v` whose `c` mentions neither `v` nor an inner binder.
    Return `c` together with a proof of `v = c` built from `h`. -/
private partial def pinProof (v : Expr) (bound : Array FVarId) (e h : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let e ← instantiateMVars e
  let ok (c : Expr) : Bool :=
    !c.containsFVar v.fvarId! && bound.all (fun b => !c.containsFVar b)
  if let some (_, lhs, rhs) := e.eq? then
    if lhs == v && ok rhs then return some (rhs, h)
    if rhs == v && ok lhs then return some (lhs, ← mkEqSymm h)
    return none
  if e.isAppOfArity ``And 2 then
    let l := e.appFn!.appArg!
    let r := e.appArg!
    if let some res ← pinProof v bound l (mkApp3 (mkConst ``And.left) l r h) then
      return some res
    return ← pinProof v bound r (mkApp3 (mkConst ``And.right) l r h)
  if e.isAppOfArity ``Exists 2 then
    let α := e.appFn!.appArg!
    let p := e.appArg!
    let u ← getLevel α
    return ← withLocalDeclD `w α fun w => do
      let pw := (mkApp p w).headBeta
      withLocalDeclD `hw pw fun hw => do
        let some (c, prf) ← pinProof v (bound.push w.fvarId!) pw hw | return none
        let goal ← mkEq v c
        let fn ← mkLambdaFVars #[w, hw] prf
        return some (c, mkApp5 (mkConst ``Exists.elim (u :: [])) α p goal h fn)
  return none

/-- **Witness pinning as a simproc.**  Rewrites `∃ v, body` to `body[c/v]`
    whenever `body` contains a conjunct `v = c` (or `c = v`) anywhere below
    `∧` and inner `∃`, not only next to the binder as `exists_eq_left`
    requires.  Unlike the goal-level `il_pin` it works everywhere `simp`
    reaches: inside disjunctions (one per path of an unrolled loop or an
    `if`), in hypotheses, and under other binders.  Proof: `exists_pin_eq`
    with the projection of the pinning conjunct built by `pinProof`.
    Declared with `simproc_decl`, i.e. NOT in the default simp set: only the
    MapLang closers (`il_simp`, `il_simp_ac`) use it. -/
simproc_decl existsPin (Exists _) := fun e => do
  let_expr Exists α p := e | return .continue
  let u ← getLevel α
  let res ← withLocalDeclD `v α fun v => do
    let body := (mkApp p v).headBeta
    withLocalDeclD `hb body fun hb => do
      let some (c, prf) ← pinProof v #[] body hb | return none
      return some (c, ← mkLambdaFVars #[v, hb] prf)
  let some (c, h) := res | return .continue
  let proof := mkApp4 (mkConst ``exists_pin_eq (u :: [])) α p c h
  return .visit { expr := (mkApp p c).headBeta, proof? := some proof }

-- ============================================================
-- Leaf tactics
-- ============================================================

/-- Arithmetic leaf: `omega` only recognises `Nat`, so first unfold the
    `Ty.denote .nat` type annotations produced by typed reads. -/
scoped elab "il_arith" : tactic => do
  evalTactic (← `(tactic| ((try dsimp only [Ty.denote] at *); omega)))

/-- The MapLang simp set (used by every closer). -/
scoped elab "il_simp" : tactic => do
  evalTactic (← `(tactic|
    simp_all [existsPin, exists_const, exists_eq_left, exists_eq_right, exists_eq_left',
              exists_eq_right', exists_and_eq_add, exists_and_add_eq, Ref.mk.injEq, Ref.null]))

/-- `il_simp` with a larger step budget, for fully unrolled VCs: a program
    with two loops unrolled together (sorted-array insert: scan + shift) needs
    more than the default 100 000 simp steps. -/
scoped elab "il_simp_unrolled" : tactic => do
  evalTactic (← `(tactic|
    simp_all (config := { maxSteps := 5000000 })
      [existsPin, exists_const, exists_eq_left, exists_eq_right, exists_eq_left',
       exists_eq_right', exists_and_eq_add, exists_and_add_eq, Ref.mk.injEq, Ref.null]))

/-- The MapLang simp set with AC-normalisation of `∧`. -/
scoped elab "il_simp_ac" : tactic => do
  evalTactic (← `(tactic|
    simp_all [existsPin, exists_const, exists_eq_left, exists_eq_right, exists_eq_left',
              exists_eq_right', exists_and_eq_add, exists_and_add_eq, Ref.mk.injEq, Ref.null,
              and_assoc, and_comm, and_left_comm]))

/-- Search the body of `∃ v, body` (through `∧` and inner `∃`) for a
    conjunct `v = c` or `c = v` whose other side is closed (no bound
    variable), and return that `c`. -/
private partial def findPin (depth : Nat) (e : Expr) : Option Expr :=
  match e with
  | .app (.app (.const ``And _) l) r => findPin depth l <|> findPin depth r
  | .app (.app (.const ``Exists _) _) (.lam _ _ b _) => findPin (depth + 1) b
  | e =>
    match e.eq? with
    | some (_, lhs, rhs) =>
      if lhs == .bvar depth && !rhs.hasLooseBVars then some rhs
      else if rhs == .bvar depth && !lhs.hasLooseBVars then some lhs
      else none
    | none => none

/-- **Witness pinning.**  On a goal `∃ v, body`, find a conjunct `v = c`
    (anywhere in `body`, even buried after conjuncts that mention `v`) and
    instantiate the witness with `c`.  This is what the plain `exists_eq_*`
    simp lemmas cannot do when the pinning equation is not adjacent to the
    binder. -/
scoped elab "il_pin" : tactic => do
  let goal ← getMainGoal
  let ty ← instantiateMVars (← goal.getType)
  let ty ← whnfR ty
  let_expr Exists _ f := ty | throwError "il_pin: goal is not an existential"
  let body ← match f with
    | .lam _ _ b _ => pure b
    | _ => throwError "il_pin: expected a lambda"
  let some c := findPin 0 body | throwError "il_pin: no pinning equation found"
  let cStx ← Lean.Elab.Term.exprToSyntax c
  evalTactic (← `(tactic| refine ⟨$cStx, ?_⟩))

/-- Split a conjunction goal (and nothing else). -/
scoped elab "il_and_split" : tactic => do
  let goal ← getMainGoal
  let ty ← whnfR (← instantiateMVars (← goal.getType))
  let_expr And _ _ := ty | throwError "il_and_split: goal is not a conjunction"
  evalTactic (← `(tactic| refine ⟨?_, ?_⟩))

/-- Repeatedly pin witnesses (splitting conjunctions on the way) and re-simplify. -/
scoped elab "il_pins" : tactic => do
  -- NB: `repeat` recurses into generated subgoals by itself; wrapping the body
  -- in `all_goals` would loop forever once no goals are left.
  evalTactic (← `(tactic|
    repeat (first | (il_pin; try il_simp) | (il_and_split; try il_simp))))

/-- `decide`, but only on a *closed* goal (no free variables): on open goals
    `decide` unfolds instances deeply before failing and wastes heartbeats. -/
scoped elab "il_decide_closed" : tactic => do
  let ty ← instantiateMVars (← getMainTarget)
  if ty.hasFVar || ty.hasMVar then throwError "il_decide_closed: goal is not closed"
  evalTactic (← `(tactic| decide))

/-- Leaf finisher: arithmetic, or `decide` for closed bounded existentials such
    as `∃ i, i ≤ 2 ∧ …` that survive simplification. -/
scoped elab "il_leaf" : tactic => do
  evalTactic (← `(tactic| first | il_arith | il_decide_closed))

-- ============================================================
-- Closers
-- ============================================================

/-- Atomic closer: simp, witness pinning, then up to three levels of `split`
    (for `if` on symbolic indices), each followed by arithmetic. -/
scoped elab "il_close_atom" : tactic => do
  evalTactic (← `(tactic|
    first
      | (intros
         il_simp
         all_goals (try il_pins)
         all_goals il_leaf
         done)
      | (intros
         il_simp
         all_goals (try il_pins)
         all_goals (split <;> il_leaf)
         done)
      | (intros
         il_simp
         all_goals (try il_pins)
         all_goals (split <;> split <;> il_leaf)
         done)
      | (intros
         il_simp
         all_goals (try il_pins)
         all_goals (split <;> split <;> split <;> il_leaf)
         done)))

/-- Enumerates left/right paths through up to three levels of disjunction
    (sequences of `if`, bounded unrolling), trying `il_close_atom` at each leaf. -/
scoped elab "il_close" : tactic => do
  evalTactic (← `(tactic| first
    | il_close_atom
    | (left; il_close_atom)
    | (right; il_close_atom)
    | (left; left; il_close_atom)
    | (left; right; il_close_atom)
    | (right; left; il_close_atom)
    | (right; right; il_close_atom)
    | (left; left; left; il_close_atom)
    | (left; left; right; il_close_atom)
    | (left; right; left; il_close_atom)
    | (left; right; right; il_close_atom)
    | (right; left; left; il_close_atom)
    | (right; left; right; il_close_atom)
    | (right; right; left; il_close_atom)
    | (right; right; right; il_close_atom)))

/-- AC-normalising fallback: floats a determining equation buried inside a
    multi-clause invariant next to its binding `∃` so it can be eliminated. -/
scoped elab "il_close_ac" : tactic => do
  evalTactic (← `(tactic|
    first
      | (intros
         il_simp_ac
         all_goals (try il_pins)
         all_goals il_leaf
         done)
      | (intros
         il_simp_ac
         all_goals (try il_pins)
         all_goals (split <;> il_leaf)
         done)))

/-- Two-tier closer: cheap path first, AC fallback second. -/
scoped elab "il_close_hard" : tactic => do
  evalTactic (← `(tactic| first | il_close | il_close_ac))

-- ============================================================
-- SP unfolding (shared by the provers below)
-- ============================================================

/-- Rewrite `sp` into its first-order elimination forms. -/
scoped elab "il_unfold_sp" : tactic => do
  evalTactic (← `(tactic| simp only [unroll_while, sp_skip', sp_assign, sp_mapUpdate,
                            sp_alloc, sp_setInsert, sp_setRemove, sp_relInsert, sp_relRemove,
                            sp_seq', sp_ite', sp_assume', sp_assert']))

-- ============================================================
-- Bounded while
-- ============================================================

/-- Fail if the goal is literally `False`.  After simplification this is
    what an unrolling depth that is too small produces (no path of at most
    `k` iterations reaches the target state), so the search can move on at
    once instead of running the expensive closers on a refuted goal. -/
scoped elab "il_nonfalse" : tactic => do
  let ty ← instantiateMVars (← getMainTarget)
  if ty.isConstOf ``False then throwError "il_nonfalse: goal simplified to False"

/-- Closer for fully unrolled VCs: simplify once (with `existsPin` this
    usually closes the goal), fail fast on a refuted goal, otherwise try
    `il_close`.  The AC fallback is deliberately NOT used here: on a
    refuted-but-not-`False` goal it can exhaust the heartbeat budget, and a
    heartbeat timeout is not caught by `first`, so it would abort the whole
    unrolling-depth search. -/
scoped elab "il_close_unrolled" : tactic => do
  evalTactic (← `(tactic|
    (intros
     try il_simp_unrolled
     all_goals il_nonfalse
     all_goals il_close)))

/-- Heartbeat budget (in thousands, like `maxHeartbeats`) of ONE unrolling
    depth attempt.  Five times the default, enough for the sorted-array insert
    (two loops, unrolled together). -/
def unrollHeartbeats : Nat := 1000000

/-- `incorrectness_auto_while N`: unroll EVERY loop of the program `N` times
    (`vc_unroll_sound`) and close the resulting loop-free VC.  The loops need
    not be at the top: a scan loop followed by a splice, or two loops in
    sequence, are handled without a hand-written midpoint (`seq_intro`). -/
scoped syntax "incorrectness_auto_while" num : tactic
scoped elab_rules : tactic
  | `(tactic| incorrectness_auto_while $k) => do
    -- Each unrolling depth gets its own heartbeat budget (counted from now,
    -- limit `unrollHeartbeats`), so that failed shallower depths tried by
    -- `incorrectness_auto_while_search` do not eat the budget of the depth
    -- that succeeds.
    withCurrHeartbeats <| withTheReader Core.Context
        (fun ctx => { ctx with maxHeartbeats := unrollHeartbeats * 1000 }) do
      evalTactic (← `(tactic| apply vc_unroll_sound $k))
      evalTactic (← `(tactic| intro _ _))
      evalTactic (← `(tactic| simp only [unrollAll]))
      evalTactic (← `(tactic| il_unfold_sp))
      evalTactic (← `(tactic| il_close_unrolled))

/-- Try `incorrectness_auto_while N` for `N = 0..10`. -/
scoped elab "incorrectness_auto_while_search" : tactic => do
  evalTactic (← `(tactic| first
    | incorrectness_auto_while 0
    | incorrectness_auto_while 1
    | incorrectness_auto_while 2
    | incorrectness_auto_while 3
    | incorrectness_auto_while 4
    | incorrectness_auto_while 5
    | incorrectness_auto_while 6
    | incorrectness_auto_while 7
    | incorrectness_auto_while 8
    | incorrectness_auto_while 9
    | incorrectness_auto_while 10))

-- ============================================================
-- Unified dispatcher
-- ============================================================

/-- Fail if the program in the goal contains a `while` loop.  (Loops hidden
    behind a named definition are not seen; `incorrectness_auto` is meant for
    programs written out in the goal.) -/
scoped elab "il_loop_free" : tactic => do
  let ty ← instantiateMVars (← getMainTarget)
  if (ty.find? (·.isConstOf ``Stmt.whileDo)).isSome then
    throwError "il_loop_free: the program contains a loop"

/-- Loop-free path: `vc_sound` + sp unfolding + `il_close_hard`.  Only for
    programs without loops: on a loop the semantic `sp` clause stays opaque
    and the AC fallback of `il_close_hard` can exhaust the heartbeat budget,
    which `first` does not catch. -/
scoped elab "incorrectness_auto_lf" : tactic => do
  evalTactic (← `(tactic| il_loop_free))
  evalTactic (← `(tactic| apply vc_sound))
  evalTactic (← `(tactic| intro _ _))
  evalTactic (← `(tactic| first
    | assumption
    | (il_unfold_sp; il_close_hard)))

/-- **Automated IL prover.**  Loop-free path first, then bounded unrolling. -/
scoped elab "incorrectness_auto" : tactic => do
  evalTactic (← `(tactic| first
    | incorrectness_auto_lf
    | incorrectness_auto_while_search))

-- ============================================================
-- Invariant-hint while
-- ============================================================

/-- `incorrectness_auto_inv inv`: indexed-invariant VC, all three goals
    closed by `il_close_hard`. -/
scoped syntax "incorrectness_auto_inv" term : tactic
scoped elab_rules : tactic
  | `(tactic| incorrectness_auto_inv $inv) => do
    evalTactic (← `(tactic| apply vc_while_inv_sound (Inv := $inv)))
    evalTactic (← `(tactic|
      all_goals (first
        | il_close_hard
        | (intro _ _; il_unfold_sp; il_close_hard)
        | (intro _ _ _; il_unfold_sp; il_close_hard))))

/-- Builds the nested case split on the iteration counter `x ∈ {0, …, bound}`. -/
private partial def mkSplitTac (x : Ident) (k : Nat) (bound : Nat) :
    TacticM (TSyntax ``Lean.Parser.Tactic.tacticSeq) := do
  if k ≥ bound then
    `(tacticSeq|
        have hieq : $x = $(quote bound) := by omega
        subst hieq
        il_close_hard)
  else
    let inner ← mkSplitTac x (k+1) bound
    `(tacticSeq|
        rcases Nat.lt_or_ge $x $(quote (k+1)) with hcase | hcase
        · have hieq : $x = $(quote k) := by omega
          subst hieq
          il_close_hard
        · $inner)

/-- `il_close_split_at x N`: case-split `x = 0, …, N` and close each branch. -/
scoped syntax "il_close_split_at" ident num : tactic
scoped elab_rules : tactic
  | `(tactic| il_close_split_at $x:ident $n:num) => do
    let splitTac ← mkSplitTac x 0 n.getNat
    evalTactic (← `(tactic| first | il_close | $splitTac))

/-- `incorrectness_auto_inv_split N inv`: invariant VC + iteration case split. -/
scoped syntax "incorrectness_auto_inv_split" num term : tactic
scoped elab_rules : tactic
  | `(tactic| incorrectness_auto_inv_split $n:num $inv:term) => do
    evalTactic (← `(tactic|
      (apply vc_while_inv_sound (Inv := $inv)
       all_goals (first
         | il_close
         | (intro _ _; il_unfold_sp; il_close)
         | (intro i _ _; il_unfold_sp; il_close_split_at i $n)))))

end MapLang
