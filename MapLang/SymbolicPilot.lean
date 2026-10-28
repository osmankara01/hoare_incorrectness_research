import MapLang.SymbolicSet

/-!
# Pilot measurement: how much of the symbolic set does today's automation close?

Every `example` below is tried independently; a failure in one does not stop
the others. Run:

    lake build MapLang.SymbolicSet
    lake env lean MapLang/SymbolicPilot.lean

Every `example` that reports no error counts as **closed**. There are no
manual proof steps:

* groups A and B: only `incorrectness_auto`;
* group C: only a loop invariant + `incorrectness_auto_inv`.
  C05 (two loops) and C06 (scan + splice) need an intermediate assertion as
  well, which is not written yet; they are tried here with
  `incorrectness_auto` alone.

Baseline (29 October 2026, Lean 4.35.0):

| Group | Closed | Not closed |
|---|---|---|
| A (loop-free, symbolic values) | 11/13 | A07, A13 |
| B (loops, symbolic values)     | 4/11: B04, B07, B10, B11 | B01, B02, B03, B05, B06, B08, B09 |
| C (loops, arbitrary size)      | 5/11: C01, C02, C03, C04, C07 | C08, C09, C10, C11; C05, C06 first tried in this version |
-/

namespace MapLang.Examples

-- ---------------- A: loop-free, symbolic values ----------------
example : A01 := by unfold A01; intros; incorrectness_auto
example : A02 := by unfold A02; intros; incorrectness_auto
example : A03 := by unfold A03; intros; incorrectness_auto
example : A04 := by unfold A04; intros; incorrectness_auto
example : A05 := by unfold A05; intros; incorrectness_auto
example : A06 := by unfold A06; intros; incorrectness_auto
example : A07 := by unfold A07; intros; incorrectness_auto
example : A08 := by unfold A08; intros; incorrectness_auto
example : A09 := by unfold A09; intros; incorrectness_auto
example : A10 := by unfold A10; intros; incorrectness_auto
example : A11 := by unfold A11; intros; incorrectness_auto
example : A12 := by unfold A12; intros; incorrectness_auto
example : A13 := by unfold A13; intros; incorrectness_auto

-- ---------------- B: loops, symbolic values ----------------
example : B01 := by unfold B01; intros; incorrectness_auto
example : B02 := by unfold B02; intros; incorrectness_auto
example : B03 := by unfold B03; intros; incorrectness_auto
example : B04 := by unfold B04; intros; incorrectness_auto
example : B05 := by unfold B05; intros; incorrectness_auto
example : B06 := by unfold B06; intros; incorrectness_auto
example : B07 := by unfold B07; intros; incorrectness_auto
example : B08 := by unfold B08; intros; incorrectness_auto
example : B09 := by unfold B09; intros; incorrectness_auto
example : B10 := by unfold B10; intros; incorrectness_auto
example : B11 := by unfold B11; intros; incorrectness_auto

-- ---------------- C: loops, arbitrary size (invariant only) ----------------
example : C01 := by
  unfold C01
  incorrectness_auto_inv (fun k s => s⟦x⟧ = k ∧ k ≤ s⟦N⟧ + 1)

example : C02 := by
  unfold C02
  incorrectness_auto_inv (fun k s => s⟦counter⟧ = k ∧ k ≤ s⟦N⟧)

example : C03 := by
  unfold C03
  incorrectness_auto_inv (fun k s => s⟦requests⟧ = k ∧ k ≤ s⟦N⟧)

example : C04 := by
  unfold C04
  incorrectness_auto_inv (fun k s => s⟦x⟧ = k ∧ s⟦y⟧ = k ∧ k ≤ s⟦N⟧)

-- C05: two loops; tried with the automatic tactic alone (no invariant yet).
example : C05 := by unfold C05; intros; incorrectness_auto

-- C06 (the advisor's example): tried with the automatic tactic alone
-- (no invariant / intermediate assertion yet).
example : C06 := by unfold C06; intros; incorrectness_auto

example : C07 := by
  unfold C07
  incorrectness_auto_inv (fun k s =>
    s⟦i⟧ = k + 1 ∧ k ≤ s⟦N⟧ ∧ 1 ≤ s⟦N⟧ ∧
    s⟦curr⟧ = (if k + 1 ≤ s⟦N⟧ then Ref.mk (k + 1) else Ref.null) ∧
    s⟦prev⟧ = (if k = 0 then Ref.null else Ref.mk k) ∧
    ∀ j, 1 ≤ j → j ≤ s⟦N⟧ → s⟦next⟧ ⟨j⟩ = if j + 1 ≤ s⟦N⟧ then ⟨j + 1⟩ else Ref.null)

example : C08 := by
  unfold C08
  intro k
  incorrectness_auto_inv (fun m s =>
    s⟦len⟧ = s⟦N⟧ ∧ k + 1 < s⟦N⟧ ∧
    (∀ m', m' < k → s⟦a⟧ m' < s⟦target⟧) ∧ s⟦a⟧ k = s⟦target⟧ ∧
    (∀ m', k < m' → m' < s⟦N⟧ → s⟦a⟧ m' > s⟦target⟧) ∧
    s⟦i⟧ = m ∧ m ≤ k + 2 ∧
    (m ≤ k + 1 → s⟦pos⟧ = s⟦N⟧) ∧ (m = k + 2 → s⟦pos⟧ = k + 1))

example : C09 := by
  unfold C09
  incorrectness_auto_inv (fun k s =>
    1 ≤ s⟦N⟧ ∧ s⟦target⟧ = s⟦N⟧ ∧ k ≤ s⟦N⟧ ∧
    (∀ m, 1 ≤ m → m ≤ s⟦N⟧ → s⟦key⟧ ⟨m⟩ = m) ∧
    (∀ m, 1 ≤ m → m ≤ s⟦N⟧ → s⟦next⟧ ⟨m⟩ = if m + 1 ≤ s⟦N⟧ then ⟨m + 1⟩ else Ref.null) ∧
    s⟦curr⟧ = (if k + 1 ≤ s⟦N⟧ then Ref.mk (k + 1) else Ref.null) ∧
    s⟦prev⟧ = (if k = 0 then Ref.null else Ref.mk k))

example : C10 := by
  unfold C10
  incorrectness_auto_inv (fun k s =>
    1 ≤ s⟦N⟧ ∧ k ≤ s⟦N⟧ ∧
    (∀ m, 1 ≤ m → m ≤ s⟦N⟧ → s⟦next⟧ ⟨m⟩ = if m + 1 ≤ s⟦N⟧ then ⟨m + 1⟩ else Ref.null) ∧
    s⟦curr⟧ = (if k + 1 ≤ s⟦N⟧ then Ref.mk (k + 1) else Ref.null) ∧
    s⟦visited⟧ Ref.null = decide (k = s⟦N⟧) ∧ s⟦visited⟧ ⟨1⟩ = false ∧
    (∀ m, 2 ≤ m → m ≤ s⟦N⟧ → s⟦visited⟧ ⟨m⟩ = decide (m ≤ k + 1)))

example : C11 := by
  unfold C11
  incorrectness_auto_inv (fun k s =>
    s⟦i⟧ = k ∧ k ≤ s⟦N⟧ ∧
    (∀ m, m < s⟦N⟧ → s⟦src⟧ m = ⟨m + 1⟩ ∧ s⟦dst⟧ m = ⟨m + 2⟩) ∧
    (∀ m, m < s⟦N⟧ → s⟦E⟧ ⟨m + 1⟩ ⟨m + 2⟩ = false) ∧
    (∀ m, m < s⟦N⟧ → s⟦E⟧ ⟨m + 2⟩ ⟨m + 1⟩ = decide (m < k)))

end MapLang.Examples
