import MapLang.Core

/-!
# Incorrectness-logic triples and proof rules for MapLang

`[* P *] (S) [* Q *]` — O'Hearn's under-approximate triple: **every** state
satisfying `Q` is reachable from **some** state satisfying `P` by running
`S`.  The rules below are the MapLang counterparts of the files
`Incorrectness/{Skip,Assign,Seq,If,While,Cons,Frame,Assert,Assume}.lean`,
plus the new atomic rules (`mapUpdate`, `alloc`, `setInsert`, `setRemove`,
`relInsert`, `relRemove`).
-/

namespace MapLang

/-- The incorrectness (under-approximate) triple. -/
def Triple (P : State → Prop) (S : Stmt) (Q : State → Prop) : Prop :=
  ∀ t, Q t → ∃ s, P s ∧ (S, s) ⟹ t

scoped notation "[* " P " *] " "(" S ")" " [* " Q " *]" => Triple P S Q

-- ------------------------------------------------------------
-- Atomic statements
-- ------------------------------------------------------------

/-- `[P] skip [P]` -/
theorem skip_intro {P : State → Prop} : [* P *] (Stmt.skip) [* P *] := by
  intro t hP
  exact ⟨t, hP, BigStep.skip t⟩

/-- Floyd-style assignment rule, for a variable of *any* type. -/
theorem assign_intro {P : State → Prop} {τ : Ty} {x : Var τ} {e : State → τ.denote} :
    [* P *] (Stmt.assign x e) [* fun t => ∃ s, P s ∧ t = s[x ↦ e s] *] := by
  rintro t ⟨s, hP, rfl⟩
  exact ⟨s, hP, BigStep.assign x e s⟩

/-- Map-update rule `m[k] := v`. -/
theorem mapUpdate_intro {P : State → Prop} {a b : Ty} [DecidableEq a.denote]
    {m : Var (.map a b)} {k : State → a.denote} {v : State → b.denote} :
    [* P *] (Stmt.mapUpdate m k v) [* fun t => ∃ s, P s ∧ t = s.mapUpd m (k s) (v s) *] := by
  rintro t ⟨s, hP, rfl⟩
  exact ⟨s, hP, BigStep.mapUpdate m k v s⟩

/-- Allocation rule `x := new`: the new node is some fresh, non-NULL `r`. -/
theorem alloc_intro {P : State → Prop} {x : Var .ref} :
    [* P *] (Stmt.alloc x)
    [* fun t => ∃ s r, P s ∧ s.alloc r = false ∧ r ≠ Ref.null ∧ t = s.doAlloc x r *] := by
  rintro t ⟨s, r, hP, hfresh, hnn, rfl⟩
  exact ⟨s, hP, BigStep.alloc x r s hfresh hnn⟩

/-- Set-insertion rule `S := S ∪ {k}`. -/
theorem setInsert_intro {P : State → Prop} {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} :
    [* P *] (Stmt.setInsert S k) [* fun t => ∃ s, P s ∧ t = s.setIns S (k s) *] := by
  rintro t ⟨s, hP, rfl⟩
  exact ⟨s, hP, BigStep.setInsert S k s⟩

/-- Set-removal rule `S := S \ {k}`. -/
theorem setRemove_intro {P : State → Prop} {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} :
    [* P *] (Stmt.setRemove S k) [* fun t => ∃ s, P s ∧ t = s.setRem S (k s) *] := by
  rintro t ⟨s, hP, rfl⟩
  exact ⟨s, hP, BigStep.setRemove S k s⟩

/-- Sanity check on the semantics: `S.insert k` behaves exactly like the map
    write `S[k] := true` (same final states from every initial state). -/
theorem setInsert_iff_mapUpdate {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} {s t : State} :
    (Stmt.setInsert S k, s) ⟹ t ↔ (Stmt.mapUpdate S k (fun _ => true), s) ⟹ t := by
  constructor
  · intro h
    cases h
    exact BigStep.mapUpdate _ _ _ _
  · intro h
    cases h
    exact BigStep.setInsert _ _ _

/-- `S.remove k` behaves exactly like the map write `S[k] := false`. -/
theorem setRemove_iff_mapUpdate {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} {s t : State} :
    (Stmt.setRemove S k, s) ⟹ t ↔ (Stmt.mapUpdate S k (fun _ => false), s) ⟹ t := by
  constructor
  · intro h
    cases h
    exact BigStep.mapUpdate _ _ _ _
  · intro h
    cases h
    exact BigStep.setRemove _ _ _

/-- Relation-insertion rule `R := R ∪ {(x, y)}`. -/
theorem relInsert_intro {P : State → Prop} {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] {R : Var (.map a (.map b .bool))}
    {x : State → a.denote} {y : State → b.denote} :
    [* P *] (Stmt.relInsert R x y) [* fun t => ∃ s, P s ∧ t = s.relIns R (x s) (y s) *] := by
  rintro t ⟨s, hP, rfl⟩
  exact ⟨s, hP, BigStep.relInsert R x y s⟩

/-- Relation-removal rule `R := R \ {(x, y)}`. -/
theorem relRemove_intro {P : State → Prop} {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] {R : Var (.map a (.map b .bool))}
    {x : State → a.denote} {y : State → b.denote} :
    [* P *] (Stmt.relRemove R x y) [* fun t => ∃ s, P s ∧ t = s.relRem R (x s) (y s) *] := by
  rintro t ⟨s, hP, rfl⟩
  exact ⟨s, hP, BigStep.relRemove R x y s⟩

/-- Sanity check on the semantics: the statement `R.insert (x, y)` behaves
    exactly like the whole-relation assignment `R := RelV.insert x y R`. -/
theorem relInsert_iff_assign {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
    {R : Var (.map a (.map b .bool))} {x : State → a.denote} {y : State → b.denote}
    {s t : State} :
    (Stmt.relInsert R x y, s) ⟹ t ↔
      (Stmt.assign R (fun s => RelV.insert (x s) (y s) (s⟦R⟧)), s) ⟹ t := by
  constructor
  · intro h
    cases h
    exact BigStep.assign _ _ _
  · intro h
    cases h
    exact BigStep.relInsert _ _ _ _

/-- `R.remove (x, y)` behaves exactly like `R := RelV.erase x y R`. -/
theorem relRemove_iff_assign {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
    {R : Var (.map a (.map b .bool))} {x : State → a.denote} {y : State → b.denote}
    {s t : State} :
    (Stmt.relRemove R x y, s) ⟹ t ↔
      (Stmt.assign R (fun s => RelV.erase (x s) (y s) (s⟦R⟧)), s) ⟹ t := by
  constructor
  · intro h
    cases h
    exact BigStep.assign _ _ _
  · intro h
    cases h
    exact BigStep.relRemove _ _ _ _

theorem assume_intro {P B : State → Prop} :
    [* fun s => P s ∧ B s *] (Stmt.assume B) [* fun s => P s ∧ B s *] := by
  rintro t ⟨hP, hB⟩
  exact ⟨t, ⟨hP, hB⟩, BigStep.assume B t hB⟩

theorem assert_intro {P B : State → Prop} :
    [* P *] (Stmt.assert B) [* P *] := by
  intro t hP
  by_cases hB : B t
  · exact ⟨t, hP, BigStep.assert_ok B t hB⟩
  · exact ⟨t, hP, BigStep.assert_er B t hB⟩

-- ------------------------------------------------------------
-- Compound statements
-- ------------------------------------------------------------

theorem seq_intro {P Q R : State → Prop} {S T : Stmt}
    (h1 : [* P *] (S) [* Q *]) (h2 : [* Q *] (T) [* R *]) :
    [* P *] (S; T) [* R *] := by
  intro u hR
  obtain ⟨t, hQ, hT⟩ := h2 u hR
  obtain ⟨s, hP, hS⟩ := h1 t hQ
  exact ⟨s, hP, BigStep.seq S T s t u hS hT⟩

theorem if_then {P Q B : State → Prop} {S T : Stmt}
    (h : [* fun s => P s ∧ B s *] (S) [* Q *]) :
    [* P *] (Stmt.ifThenElse B S T) [* Q *] := by
  intro t hQ
  obtain ⟨s, ⟨hP, hB⟩, hS⟩ := h t hQ
  exact ⟨s, hP, BigStep.if_true B S T s t hB hS⟩

theorem if_else {P Q B : State → Prop} {S T : Stmt}
    (h : [* fun s => P s ∧ ¬ B s *] (T) [* Q *]) :
    [* P *] (Stmt.ifThenElse B S T) [* Q *] := by
  intro t hQ
  obtain ⟨s, ⟨hP, hB⟩, hT⟩ := h t hQ
  exact ⟨s, hP, BigStep.if_false B S T s t hB hT⟩

/-- Zero-iteration while rule. -/
theorem while_intro {P B : State → Prop} {S : Stmt} :
    [* P *] (Stmt.whileDo B S) [* fun t => P t ∧ ¬ B t *] := by
  rintro t ⟨hP, hB⟩
  exact ⟨t, hP, BigStep.while_false B S t hB⟩

theorem while_iterations_aux {P : Nat → State → Prop} {B : State → Prop} {S : Stmt}
    (hBody : ∀ i, [* fun s => P i s ∧ B s *] (S) [* fun s => P (i + 1) s *]) :
    ∀ n sn t, P n sn → (Stmt.whileDo B S, sn) ⟹ t →
      ∃ s0, P 0 s0 ∧ (Stmt.whileDo B S, s0) ⟹ t := by
  intro n
  induction n with
  | zero => intro s0 t hP0 hExec; exact ⟨s0, hP0, hExec⟩
  | succ n ih =>
    intro sn1 t hPsucc hExec
    obtain ⟨sn, ⟨hPn, hBsn⟩, hStep⟩ := hBody n sn1 hPsucc
    exact ih sn t hPn (BigStep.while_true B S sn sn1 t hBsn hStep hExec)

/-- Indexed-invariant while rule (O'Hearn's backwards variant). -/
theorem while_intro_paper {P : Nat → State → Prop} {B : State → Prop} {S : Stmt}
    (hBody : ∀ i, [* fun s => P i s ∧ B s *] (S) [* fun s => P (i + 1) s *]) :
    [* P 0 *] (Stmt.whileDo B S) [* fun t => ¬ B t ∧ ∃ i, P i t *] := by
  rintro t ⟨hNotB, i, hPi⟩
  exact while_iterations_aux hBody i t t hPi (BigStep.while_false B S t hNotB)

-- ------------------------------------------------------------
-- Structural rules
-- ------------------------------------------------------------

/-- Consequence: strengthen the pre, weaken (shrink) the post. -/
theorem consequence {P P' Q Q' : State → Prop} {S : Stmt}
    (hP : ∀ s, P' s → P s) (hTriple : [* P' *] (S) [* Q' *]) (hQ : ∀ s, Q s → Q' s) :
    [* P *] (S) [* Q *] := by
  intro t hQt
  obtain ⟨s, hP's, hExec⟩ := hTriple t (hQ t hQt)
  exact ⟨s, hP s hP's, hExec⟩

/-- Frame: a property preserved backwards by `S` can be added to both sides. -/
theorem frame {P Q R : State → Prop} {S : Stmt}
    (hTriple : [* P *] (S) [* Q *])
    (hFrame : ∀ s t, R t → (S, s) ⟹ t → R s) :
    [* fun s => P s ∧ R s *] (S) [* fun t => Q t ∧ R t *] := by
  rintro t ⟨hQt, hRt⟩
  obtain ⟨s, hPs, hExec⟩ := hTriple t hQt
  exact ⟨s, ⟨hPs, hFrame s t hRt hExec⟩, hExec⟩

/-- Disjunction of postconditions. -/
theorem disj {P Q₁ Q₂ : State → Prop} {S : Stmt}
    (h₁ : [* P *] (S) [* Q₁ *]) (h₂ : [* P *] (S) [* Q₂ *]) :
    [* P *] (S) [* fun t => Q₁ t ∨ Q₂ t *] := by
  intro t ht
  cases ht with
  | inl h => exact h₁ t h
  | inr h => exact h₂ t h

end MapLang
