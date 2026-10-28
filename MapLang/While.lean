import MapLang.SP

/-!
# While loops: bounded unrolling and invariant-based VCs (MapLang)

Port of `Incorrectness/While.lean` sections 2–3 to the map language,
plus `unrollAll`, which unrolls every loop of a program (not only a
top-level one).  Nothing here depends on the value type.

* `unroll_while b c k`  — syntactic `k`-step unrolling
* `unroll_bigstep`      — an unrolled run is a run of the loop
* `vc_while_sound`      — VC for a loop with a *fixed* iteration bound
* `unrollAll k c`       — unroll EVERY loop of `c` (anywhere in it) `k` times
* `vc_unroll_sound`     — VC for whole programs through `unrollAll`
* `vc_while_inv_sound`  — VC with an indexed invariant (parametric loops)
-/

namespace MapLang

/-- Unroll a while loop `k` times into a loop-free statement. -/
def unroll_while (b : State → Prop) (c : Stmt) : Nat → Stmt
  | 0     => Stmt.assume (fun s => ¬ b s)
  | n + 1 => Stmt.ifThenElse b (Stmt.seq c (unroll_while b c n)) Stmt.skip

theorem unroll_bigstep (b : State → Prop) (c : Stmt) :
    ∀ k s t, (unroll_while b c k, s) ⟹ t → (Stmt.whileDo b c, s) ⟹ t := by
  intro k
  induction k with
  | zero =>
    intro s t h
    cases h with
    | assume _ _ hcond => exact BigStep.while_false b c s hcond
  | succ k ih =>
    intro s t h
    cases h with
    | if_true _ _ _ _ _ hcond hbody =>
      cases hbody with
      | seq _ _ _ mid _ hc hunroll =>
        exact BigStep.while_true b c s mid t hcond hc (ih mid t hunroll)
    | if_false _ _ _ _ _ hcond hbody =>
      cases hbody with
      | skip _ => exact BigStep.while_false b c s hcond

theorem unroll_sound (b : State → Prop) (c : Stmt) (k : Nat) (p q : State → Prop)
    (h : [* p *] (unroll_while b c k) [* q *]) :
    [* p *] (Stmt.whileDo b c) [* q *] := by
  intro t hq
  obtain ⟨s, hp, hexec⟩ := h t hq
  exact ⟨s, hp, unroll_bigstep b c k s t hexec⟩

/-- VC for a loop with a known iteration bound `k`. -/
theorem vc_while_sound {b : State → Prop} {c : Stmt} {k : Nat} {p q : State → Prop}
    (hvc : ∀ t, q t → sp (unroll_while b c k) p t) :
    [* p *] (Stmt.whileDo b c) [* q *] := by
  apply unroll_sound b c k p q
  exact vc_sound hvc

-- ------------------------------------------------------------
-- Unrolling every loop of a program
-- ------------------------------------------------------------

/-- Replace EVERY loop of a program by its `k`-fold unrolling: top-level loops,
    loops after a `;` or inside a branch, and loops nested in loop bodies.
    The result is loop-free, and it covers exactly the runs in which every
    loop execution takes at most `k` iterations. -/
def unrollAll (k : Nat) : Stmt → Stmt
  | .skip => .skip
  | .assign x e => .assign x e
  | @Stmt.mapUpdate a b inst m kk v => @Stmt.mapUpdate a b inst m kk v
  | .alloc x => .alloc x
  | @Stmt.setInsert a inst S kk => @Stmt.setInsert a inst S kk
  | @Stmt.setRemove a inst S kk => @Stmt.setRemove a inst S kk
  | @Stmt.relInsert a b ia ib R x y => @Stmt.relInsert a b ia ib R x y
  | @Stmt.relRemove a b ia ib R x y => @Stmt.relRemove a b ia ib R x y
  | .seq c₁ c₂ => .seq (unrollAll k c₁) (unrollAll k c₂)
  | .ifThenElse b c₁ c₂ => .ifThenElse b (unrollAll k c₁) (unrollAll k c₂)
  | .whileDo b c => unroll_while b (unrollAll k c) k
  | .assert b => .assert b
  | .assume b => .assume b

/-- Unrolling a loop whose body has itself been replaced by a refinement
    `c'` of `c` still only produces runs of the original loop. -/
theorem unroll_refines {b : State → Prop} {c c' : Stmt}
    (h : ∀ s t, (c', s) ⟹ t → (c, s) ⟹ t) :
    ∀ k s t, (unroll_while b c' k, s) ⟹ t → (Stmt.whileDo b c, s) ⟹ t := by
  intro k
  induction k with
  | zero =>
    intro s t hr
    cases hr with
    | assume _ _ hcond => exact BigStep.while_false b c s hcond
  | succ k ih =>
    intro s t hr
    cases hr with
    | if_true _ _ _ _ _ hcond hbody =>
      cases hbody with
      | seq _ _ _ mid _ hc hunroll =>
        exact BigStep.while_true b c s mid t hcond (h s mid hc) (ih mid t hunroll)
    | if_false _ _ _ _ _ hcond hbody =>
      cases hbody with
      | skip _ => exact BigStep.while_false b c s hcond

/-- Every run of the fully unrolled program is a run of the original one. -/
theorem unrollAll_refines (k : Nat) :
    ∀ (c : Stmt) (s t : State), (unrollAll k c, s) ⟹ t → (c, s) ⟹ t := by
  intro c
  induction c with
  | seq c₁ c₂ ih₁ ih₂ =>
    intro s t h
    cases h with
    | seq _ _ _ mid _ h₁ h₂ => exact BigStep.seq c₁ c₂ s mid t (ih₁ s mid h₁) (ih₂ mid t h₂)
  | ifThenElse b c₁ c₂ ih₁ ih₂ =>
    intro s t h
    cases h with
    | if_true _ _ _ _ _ hb hc => exact BigStep.if_true b c₁ c₂ s t hb (ih₁ s t hc)
    | if_false _ _ _ _ _ hb hc => exact BigStep.if_false b c₁ c₂ s t hb (ih₂ s t hc)
  | whileDo b c ih => exact unroll_refines ih k
  | _ =>
    intro s t h
    exact h

/-- **VC by unrolling every loop `k` times.**  Sound for IL because IL
    under-approximates: a state reached by the unrolled (loop-free) program is
    reached by the original program.  (The dual statement is false for Hoare
    logic, where cutting loops off would lose runs.)  Unlike `vc_while_sound`
    this also handles loops that are not at the top of the program, e.g. a
    scan loop followed by a splice, without a hand-written midpoint. -/
theorem vc_unroll_sound {c : Stmt} {p q : State → Prop} (k : Nat)
    (hvc : ∀ t, q t → sp (unrollAll k c) p t) : [* p *] (c) [* q *] := by
  intro t hq
  obtain ⟨s, hp, hrun⟩ := sp_sound (unrollAll k c) p t (hvc t hq)
  exact ⟨s, hp, unrollAll_refines k c s t hrun⟩

/-- VC with an indexed invariant `Inv : Nat → State → Prop`:
    1. `Inv 0 ⊆ P`;  2. `Inv (i+1) ⊆ sp S (Inv i ∧ B)`;  3. `Q ⊆ ¬B ∧ ∃ i, Inv i`. -/
theorem vc_while_inv_sound {B : State → Prop} {S : Stmt} {P Q : State → Prop}
    {Inv : Nat → State → Prop}
    (hPre  : ∀ s, Inv 0 s → P s)
    (hBody : ∀ i, ∀ t, Inv (i + 1) t → sp S (fun s => Inv i s ∧ B s) t)
    (hPost : ∀ t, Q t → ¬ B t ∧ ∃ i, Inv i t) :
    [* P *] (Stmt.whileDo B S) [* Q *] :=
  consequence hPre (while_intro_paper (fun i => vc_sound (hBody i))) hPost

end MapLang
