import MapLang.Triple

/-!
# Strongest postcondition for MapLang

`sp c p` is the *exact* set of states reachable from `p` by `c`.  `sp_sound`
proves `[* p *] (c) [* sp c p *]` for every program, and `vc_sound` turns a
verification condition `q ⇒ sp c p` into the triple `[* p *] (c) [* q *]`.

The **elimination lemmas** are the bridge to automation: each rewrites the
existential over a whole `State` produced by `sp` into an existential over
*first-order* data (the old value of one slot; for a map or set write the
written index and the old cell; for a relation write the written pair and
its old membership bit; for `new` the fresh address and the old value of the
pointer variable).  No existential over a function is ever introduced by
`mapUpdate`, the set and relation writes, or `alloc` — that is what lets the
`il_close` family of tactics carry over unchanged in spirit.
-/

namespace MapLang

-- ============================================================
-- sp
-- ============================================================

/-- Strongest postcondition.  The `while` clause is semantic (exact
    reachability), as in `Incorrectness/SP.lean`. -/
def sp (c : Stmt) (p : State → Prop) : State → Prop :=
  match c with
  | .skip => p
  | .assign x e => fun t => ∃ s, p s ∧ t = s[x ↦ e s]
  | @Stmt.mapUpdate a b inst m k v =>
      fun t => ∃ s, p s ∧ t = @State.mapUpd s a b inst m (k s) (v s)
  | .alloc x => fun t => ∃ s r, p s ∧ s.alloc r = false ∧ r ≠ Ref.null ∧ t = s.doAlloc x r
  | @Stmt.setInsert a inst S k => fun t => ∃ s, p s ∧ t = @State.setIns s a inst S (k s)
  | @Stmt.setRemove a inst S k => fun t => ∃ s, p s ∧ t = @State.setRem s a inst S (k s)
  | @Stmt.relInsert a b ia ib R x y =>
      fun t => ∃ s, p s ∧ t = @State.relIns s a b ia ib R (x s) (y s)
  | @Stmt.relRemove a b ia ib R x y =>
      fun t => ∃ s, p s ∧ t = @State.relRem s a b ia ib R (x s) (y s)
  | .seq c₁ c₂ => sp c₂ (sp c₁ p)
  | .ifThenElse b c₁ c₂ =>
      fun t => sp c₁ (fun s => p s ∧ b s) t ∨ sp c₂ (fun s => p s ∧ ¬ b s) t
  | .whileDo B S => fun t => ∃ s, p s ∧ (Stmt.whileDo B S, s) ⟹ t
  | .assert _ => p
  | .assume B => fun s => p s ∧ B s

@[simp] theorem sp_skip' {p : State → Prop} : sp Stmt.skip p = p := rfl
@[simp] theorem sp_assign' {p : State → Prop} {τ : Ty} {x : Var τ} {e : State → τ.denote} :
    sp (Stmt.assign x e) p = fun t => ∃ s, p s ∧ t = s[x ↦ e s] := rfl
@[simp] theorem sp_mapUpdate' {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    {m : Var (.map a b)} {k : State → a.denote} {v : State → b.denote} :
    sp (Stmt.mapUpdate m k v) p = fun t => ∃ s, p s ∧ t = s.mapUpd m (k s) (v s) := rfl
@[simp] theorem sp_alloc' {p : State → Prop} {x : Var .ref} :
    sp (Stmt.alloc x) p
      = fun t => ∃ s r, p s ∧ s.alloc r = false ∧ r ≠ Ref.null ∧ t = s.doAlloc x r := rfl
@[simp] theorem sp_setInsert' {p : State → Prop} {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} :
    sp (Stmt.setInsert S k) p = fun t => ∃ s, p s ∧ t = s.setIns S (k s) := rfl
@[simp] theorem sp_setRemove' {p : State → Prop} {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} :
    sp (Stmt.setRemove S k) p = fun t => ∃ s, p s ∧ t = s.setRem S (k s) := rfl
@[simp] theorem sp_relInsert' {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] {R : Var (.map a (.map b .bool))}
    {x : State → a.denote} {y : State → b.denote} :
    sp (Stmt.relInsert R x y) p = fun t => ∃ s, p s ∧ t = s.relIns R (x s) (y s) := rfl
@[simp] theorem sp_relRemove' {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] {R : Var (.map a (.map b .bool))}
    {x : State → a.denote} {y : State → b.denote} :
    sp (Stmt.relRemove R x y) p = fun t => ∃ s, p s ∧ t = s.relRem R (x s) (y s) := rfl
@[simp] theorem sp_seq' {p : State → Prop} {c₁ c₂ : Stmt} :
    sp (c₁; c₂) p = sp c₂ (sp c₁ p) := rfl
@[simp] theorem sp_ite' {p b : State → Prop} {c₁ c₂ : Stmt} :
    sp (Stmt.ifThenElse b c₁ c₂) p
      = fun t => sp c₁ (fun s => p s ∧ b s) t ∨ sp c₂ (fun s => p s ∧ ¬ b s) t := rfl
@[simp] theorem sp_whileDo' {p B : State → Prop} {S : Stmt} :
    sp (Stmt.whileDo B S) p = fun t => ∃ s, p s ∧ (Stmt.whileDo B S, s) ⟹ t := rfl
@[simp] theorem sp_assert' {p B : State → Prop} : sp (Stmt.assert B) p = p := rfl
@[simp] theorem sp_assume' {p B : State → Prop} :
    sp (Stmt.assume B) p = fun s => p s ∧ B s := rfl

-- ============================================================
-- Elimination lemmas (first-order witnesses)
-- ============================================================

/-- Assignment: the only unknown is the *old value* `v` of the assigned slot. -/
theorem sp_assign_elim {p : State → Prop} {τ : Ty} {x : Var τ} {e : State → τ.denote}
    {t : State} :
    (∃ s, p s ∧ t = s[x ↦ e s]) ↔ ∃ v, p (t[x ↦ v]) ∧ t⟦x⟧ = e (t[x ↦ v]) := by
  constructor
  · rintro ⟨s, hp, rfl⟩
    have hss : (s[x ↦ e s])[x ↦ s⟦x⟧] = s := by
      rw [State.update_update, State.update_self]
    refine ⟨s⟦x⟧, ?_, ?_⟩
    · rw [hss]; exact hp
    · rw [hss]; exact State.update_same s x (e s)
  · rintro ⟨v, hp, heq⟩
    refine ⟨t[x ↦ v], hp, ?_⟩
    rw [← heq, State.update_update, State.update_self]

@[simp] theorem sp_assign {p : State → Prop} {τ : Ty} {x : Var τ} {e : State → τ.denote} :
    sp (Stmt.assign x e) p = fun t => ∃ v, p (t[x ↦ v]) ∧ t⟦x⟧ = e (t[x ↦ v]) := by
  funext t; exact propext sp_assign_elim

/-- Map write `m[k] := v`: the unknowns are the written index `j` and the
    old content `w` of that cell — no existential over a function.
    (The equation pinning `j` is placed first so that `simp`'s
    `exists_eq_left'` can eliminate it without AC-reordering.) -/
theorem sp_mapUpd_elim {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    {m : Var (.map a b)} {k : State → a.denote} {v : State → b.denote} {t : State} :
    (∃ s, p s ∧ t = s.mapUpd m (k s) (v s)) ↔
    ∃ (j : a.denote) (w : b.denote),
      k (t.mapUpd m j w) = j ∧ p (t.mapUpd m j w) ∧ t⟦m⟧ j = v (t.mapUpd m j w) := by
  constructor
  · rintro ⟨s, hp, rfl⟩
    have hss : (s.mapUpd m (k s) (v s)).mapUpd m (k s) (s⟦m⟧ (k s)) = s := by
      rw [State.mapUpd_mapUpd, State.mapUpd_self]
    refine ⟨k s, s⟦m⟧ (k s), ?_, ?_, ?_⟩
    · rw [hss]
    · rw [hss]; exact hp
    · rw [hss]; simp
  · rintro ⟨j, w, hk, hp, hv⟩
    refine ⟨t.mapUpd m j w, hp, ?_⟩
    rw [hk, ← hv, State.mapUpd_mapUpd, State.mapUpd_self]

@[simp] theorem sp_mapUpdate {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    {m : Var (.map a b)} {k : State → a.denote} {v : State → b.denote} :
    sp (Stmt.mapUpdate m k v) p
      = fun t => ∃ (j : a.denote) (w : b.denote),
          k (t.mapUpd m j w) = j ∧ p (t.mapUpd m j w) ∧ t⟦m⟧ j = v (t.mapUpd m j w) := by
  funext t; exact propext sp_mapUpd_elim

/-- Set insertion is the map write `S[k] := true`, so it inherits the
    first-order elimination form: the unknowns are the inserted element `j`
    and its old membership bit `w`. -/
@[simp] theorem sp_setInsert {p : State → Prop} {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} :
    sp (Stmt.setInsert S k) p
      = fun t => ∃ (j : a.denote) (w : Bool),
          k (t.mapUpd S j w) = j ∧ p (t.mapUpd S j w) ∧ t⟦S⟧ j = true := by
  funext t
  exact propext (sp_mapUpd_elim (m := S) (k := k) (v := fun _ => true))

/-- Set removal is the map write `S[k] := false`. -/
@[simp] theorem sp_setRemove {p : State → Prop} {a : Ty} [DecidableEq a.denote]
    {S : Var (.map a .bool)} {k : State → a.denote} :
    sp (Stmt.setRemove S k) p
      = fun t => ∃ (j : a.denote) (w : Bool),
          k (t.mapUpd S j w) = j ∧ p (t.mapUpd S j w) ∧ t⟦S⟧ j = false := by
  funext t
  exact propext (sp_mapUpd_elim (m := S) (k := k) (v := fun _ => false))

/-- Relation write `R[x][y] := w`: the unknowns are the written pair `(i, j)`
    and the old membership bit `v` of that pair — no existential over a row
    or a whole relation.  (The equations pinning `i` and `j` come first, as
    in `sp_mapUpd_elim`.) -/
theorem sp_relUpd_elim {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] {R : Var (.map a (.map b .bool))}
    {x : State → a.denote} {y : State → b.denote} {w : State → Bool} {t : State} :
    (∃ s, p s ∧ t = s.relUpd R (x s) (y s) (w s)) ↔
    ∃ (i : a.denote) (j : b.denote) (v : Bool),
      x (t.relUpd R i j v) = i ∧ y (t.relUpd R i j v) = j ∧ p (t.relUpd R i j v) ∧
      t⟦R⟧ i j = w (t.relUpd R i j v) := by
  constructor
  · rintro ⟨s, hp, rfl⟩
    have hss : (s.relUpd R (x s) (y s) (w s)).relUpd R (x s) (y s) (s⟦R⟧ (x s) (y s)) = s := by
      rw [State.relUpd_relUpd, State.relUpd_self]
    refine ⟨x s, y s, s⟦R⟧ (x s) (y s), ?_, ?_, ?_, ?_⟩
    · rw [hss]
    · rw [hss]
    · rw [hss]; exact hp
    · rw [hss]; simp
  · rintro ⟨i, j, v, hx, hy, hp, hw⟩
    refine ⟨t.relUpd R i j v, hp, ?_⟩
    rw [hx, hy, ← hw, State.relUpd_relUpd, State.relUpd_self]

/-- Relation insertion: the unknowns are the inserted pair `(i, j)` and its
    old membership bit `v`. -/
@[simp] theorem sp_relInsert {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] {R : Var (.map a (.map b .bool))}
    {x : State → a.denote} {y : State → b.denote} :
    sp (Stmt.relInsert R x y) p
      = fun t => ∃ (i : a.denote) (j : b.denote) (v : Bool),
          x (t.relUpd R i j v) = i ∧ y (t.relUpd R i j v) = j ∧ p (t.relUpd R i j v) ∧
          t⟦R⟧ i j = true := by
  funext t
  exact propext (sp_relUpd_elim (R := R) (x := x) (y := y) (w := fun _ => true))

/-- Relation removal: the unknowns are the removed pair `(i, j)` and its old
    membership bit `v`. -/
@[simp] theorem sp_relRemove {p : State → Prop} {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] {R : Var (.map a (.map b .bool))}
    {x : State → a.denote} {y : State → b.denote} :
    sp (Stmt.relRemove R x y) p
      = fun t => ∃ (i : a.denote) (j : b.denote) (v : Bool),
          x (t.relUpd R i j v) = i ∧ y (t.relUpd R i j v) = j ∧ p (t.relUpd R i j v) ∧
          t⟦R⟧ i j = false := by
  funext t
  exact propext (sp_relUpd_elim (R := R) (x := x) (y := y) (w := fun _ => false))

/-- Inverse of `doAlloc`: restore the pointer variable and un-mark the node. -/
def State.undoAlloc (t : State) (x : Var .ref) (r w : Ref) : State :=
  { vars  := (t[x ↦ w]).vars
    alloc := fun q => if q = r then false else t.alloc q }

@[simp] theorem State.undoAlloc_vars (t : State) (x : Var .ref) (r w : Ref) :
    (t.undoAlloc x r w).vars = (t[x ↦ w]).vars := rfl
@[simp] theorem State.undoAlloc_alloc (t : State) (x : Var .ref) (r w q : Ref) :
    (t.undoAlloc x r w).alloc q = if q = r then false else t.alloc q := rfl

/-- Allocation: the unknowns are the fresh address `r` (readable off `t`) and
    the old value `w` of the pointer variable. -/
theorem sp_alloc_elim {p : State → Prop} {x : Var .ref} {t : State} :
    (∃ s r, p s ∧ s.alloc r = false ∧ r ≠ Ref.null ∧ t = s.doAlloc x r) ↔
    ∃ (r w : Ref), t⟦x⟧ = r ∧ r ≠ Ref.null ∧ t.alloc r = true ∧ p (t.undoAlloc x r w) := by
  constructor
  · rintro ⟨s, r, hp, hfresh, hnn, rfl⟩
    have hundo : (s.doAlloc x r).undoAlloc x r (s⟦x⟧) = s := by
      refine State.ext' (fun τ y => ?_) (fun q => ?_)
      · show ((s[x ↦ r])[x ↦ s⟦x⟧]).vars τ y = s.vars τ y
        rw [State.update_update, State.update_self]
      · show (if q = r then false else (if q = r then true else s.alloc q)) = s.alloc q
        by_cases hq : q = r
        · subst hq; simp [hfresh]
        · simp [hq]
    refine ⟨r, s⟦x⟧, ?_, hnn, ?_, ?_⟩
    · exact State.update_same s x r
    · simp
    · rw [hundo]; exact hp
  · rintro ⟨r, w, hx, hnn, halloc, hp⟩
    refine ⟨t.undoAlloc x r w, r, hp, by simp, hnn, ?_⟩
    refine State.ext' (fun τ y => ?_) (fun q => ?_)
    · show t.vars τ y = ((t[x ↦ w])[x ↦ r]).vars τ y
      rw [State.update_update, State.update_eq_self t x r hx]
    · show t.alloc q = (if q = r then true else (if q = r then false else t.alloc q))
      by_cases hq : q = r
      · subst hq; simp [halloc]
      · simp [hq]

@[simp] theorem sp_alloc {p : State → Prop} {x : Var .ref} :
    sp (Stmt.alloc x) p
      = fun t => ∃ (r w : Ref), t⟦x⟧ = r ∧ r ≠ Ref.null ∧ t.alloc r = true ∧
                                p (t.undoAlloc x r w) := by
  funext t; exact propext sp_alloc_elim

-- ============================================================
-- Soundness
-- ============================================================

/-- `[* p *] (c) [* sp c p *]` for every program `c`. -/
theorem sp_sound (c : Stmt) (p : State → Prop) : [* p *] (c) [* sp c p *] := by
  induction c generalizing p with
  | skip => intro t hp; exact ⟨t, hp, BigStep.skip t⟩
  | assign x e => rintro t ⟨s, hp, rfl⟩; exact ⟨s, hp, BigStep.assign x e s⟩
  | @mapUpdate a b inst m k v =>
    rintro t ⟨s, hp, rfl⟩; exact ⟨s, hp, @BigStep.mapUpdate a b inst m k v s⟩
  | alloc x =>
    rintro t ⟨s, r, hp, hfresh, hnn, rfl⟩
    exact ⟨s, hp, BigStep.alloc x r s hfresh hnn⟩
  | @setInsert a inst S k =>
    rintro t ⟨s, hp, rfl⟩; exact ⟨s, hp, @BigStep.setInsert a inst S k s⟩
  | @setRemove a inst S k =>
    rintro t ⟨s, hp, rfl⟩; exact ⟨s, hp, @BigStep.setRemove a inst S k s⟩
  | @relInsert a b ia ib R x y =>
    rintro t ⟨s, hp, rfl⟩; exact ⟨s, hp, @BigStep.relInsert a b ia ib R x y s⟩
  | @relRemove a b ia ib R x y =>
    rintro t ⟨s, hp, rfl⟩; exact ⟨s, hp, @BigStep.relRemove a b ia ib R x y s⟩
  | seq c₁ c₂ ih₁ ih₂ =>
    intro t hsp
    obtain ⟨mid, hmid, h₂⟩ := ih₂ (sp c₁ p) t hsp
    obtain ⟨s, hp, h₁⟩ := ih₁ p mid hmid
    exact ⟨s, hp, BigStep.seq c₁ c₂ s mid t h₁ h₂⟩
  | ifThenElse b c₁ c₂ ih₁ ih₂ =>
    intro t hsp
    cases hsp with
    | inl h =>
      obtain ⟨s, ⟨hp, hb⟩, hc⟩ := ih₁ (fun s => p s ∧ b s) t h
      exact ⟨s, hp, BigStep.if_true b c₁ c₂ s t hb hc⟩
    | inr h =>
      obtain ⟨s, ⟨hp, hb⟩, hc⟩ := ih₂ (fun s => p s ∧ ¬ b s) t h
      exact ⟨s, hp, BigStep.if_false b c₁ c₂ s t hb hc⟩
  | whileDo B S _ => rintro t ⟨s, hp, hexec⟩; exact ⟨s, hp, hexec⟩
  | assert B =>
    intro t hp
    by_cases hB : B t
    · exact ⟨t, hp, BigStep.assert_ok B t hB⟩
    · exact ⟨t, hp, BigStep.assert_er B t hB⟩
  | assume B => rintro t ⟨hp, hB⟩; exact ⟨t, hp, BigStep.assume B t hB⟩

/-- Verification-condition soundness: `q ⇒ sp c p` gives `[* p *] (c) [* q *]`. -/
theorem vc_sound {c : Stmt} {p q : State → Prop} (hvc : ∀ t, q t → sp c p t) :
    [* p *] (c) [* q *] := by
  intro t hq
  exact sp_sound c p t (hvc t hq)

end MapLang
