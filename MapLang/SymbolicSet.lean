import MapLang.Examples
import MapLang.LinkedList

/-!
# Symbolic set (the frozen list of statements)

Symbolic versions of the bug catalogue in `MapLang/Examples.lean`.

The catalogue has 25 examples. All of them use concrete inputs and all of
them are closed today by a single tactic call. Each of them is transformed
here systematically (no example is picked or dropped):

* every example except Example 13 (which is already symbolic) gets a
  **symbolic-value** version: same size and iteration count, but the inputs
  are given by constraints instead of fixed numbers (24 statements);
* every example with a loop gets a **symbolic-size** version: the size of the
  array / list / bound is arbitrary (11 statements).

This gives 35 statements in three groups:

* A01–A13: loop-free programs, symbolic values (reported separately);
* B01–B11: programs with loops, symbolic values, bounded iteration count;
* C01–C11: programs with loops, arbitrary size.

Every item is a `Prop` definition and contains NO proof. The measurement is
done in `SymbolicPilot.lean`. "Closed" means: closed by a single tactic call.
For the C group the user may supply only a loop invariant (and, for
multi-phase programs, an intermediate assertion); no manual proof steps.

In catalog Examples 2, 3, 7 and 9 the constant threshold of the program is
replaced by the variable `limit`, since otherwise the bug occurs only at one
fixed value and a symbolic version would be meaningless.
-/

namespace MapLang.Examples

/-- Variable that replaces the constant threshold of catalog Examples 2, 3, 7 and 9. -/
def limit : Var .nat := ⟨"limit"⟩

-- =============================================================
-- A — loop-free programs, symbolic values (reported separately)
-- =============================================================

/-- Catalog Example 1 (withdrawal, `<` instead of `≤`): a withdrawal equal to the balance, for any value, is rejected. -/
def A01 : Prop :=
  [* fun s => s⟦withdrawal⟧ = s⟦balance⟧ *]
  (Stmt.ifThenElse (fun s => s⟦withdrawal⟧ < s⟦balance⟧)
    (Stmt.assign approved (fun _ => 1))
    (Stmt.assign approved (fun _ => 0)))
  [* fun t => t⟦approved⟧ = 0 ∧ t⟦withdrawal⟧ = t⟦balance⟧ *]

/-- Catalog Example 2 (discount threshold, constant replaced by `limit`): an amount exactly at the threshold is discounted. -/
def A02 : Prop :=
  [* fun s => s⟦amount⟧ = s⟦limit⟧ *]
  (Stmt.ifThenElse (fun s => s⟦amount⟧ ≥ s⟦limit⟧)
    (Stmt.assign discounted (fun _ => 1))
    (Stmt.assign discounted (fun _ => 0)))
  [* fun t => t⟦discounted⟧ = 1 ∧ t⟦amount⟧ = t⟦limit⟧ *]

/-- Catalog Example 3 (age check, constant replaced by `limit`): an age exactly at the threshold is rejected. -/
def A03 : Prop :=
  [* fun s => s⟦age⟧ = s⟦limit⟧ *]
  (Stmt.ifThenElse (fun s => s⟦age⟧ > s⟦limit⟧)
    (Stmt.assign allowed (fun _ => 1))
    (Stmt.assign allowed (fun _ => 0)))
  [* fun t => t⟦allowed⟧ = 0 ∧ t⟦age⟧ = t⟦limit⟧ *]

/-- Catalog Example 4 (access control, `∨` instead of `∧`): any active non-admin user gets access. -/
def A04 : Prop :=
  [* fun s => s⟦admin⟧ ≠ 1 ∧ s⟦active⟧ = 1 *]
  (Stmt.ifThenElse (fun s => s⟦admin⟧ = 1 ∨ s⟦active⟧ = 1)
    (Stmt.assign access (fun _ => 1))
    (Stmt.assign access (fun _ => 0)))
  [* fun t => t⟦access⟧ = 1 ∧ t⟦admin⟧ ≠ 1 ∧ t⟦active⟧ = 1 *]

/-- Catalog Example 7 (request validator, constant replaced by `limit`): a request exactly at the threshold is approved. -/
def A05 : Prop :=
  [* fun s => s⟦input⟧ = s⟦limit⟧ *]
  (Stmt.ifThenElse (fun s => s⟦input⟧ ≥ s⟦limit⟧)
    (Stmt.assign result (fun _ => 1))
    (Stmt.assign result (fun _ => 0)))
  [* fun t => t⟦result⟧ = 1 ∧ t⟦input⟧ = t⟦limit⟧ *]

/-- Catalog Example 9 (assertion misses a case, constant replaced by `limit`): a value at the threshold passes the assertion and reaches the error branch. -/
def A06 : Prop :=
  [* fun s => s⟦x⟧ = s⟦limit⟧ ∧ s⟦x⟧ ≠ 0 *]
  (Stmt.assert (fun s => s⟦x⟧ ≠ 0);
   Stmt.ifThenElse (fun s => s⟦x⟧ > s⟦limit⟧)
     (Stmt.assign result (fun _ => 100))
     (Stmt.assign result (fun _ => 999)))
  [* fun t => t⟦result⟧ = 999 ∧ t⟦x⟧ = t⟦limit⟧ ∧ t⟦x⟧ ≠ 0 *]

/-- Catalog set example "aliasing bug with set insert/remove": if `u` and `v` are the same (arbitrary) node, the new admin is not in the set. -/
def A07 : Prop :=
  [* fun s => s⟦u⟧ = s⟦v⟧ *]
  (Stmt.setInsert admins (fun s => s⟦u⟧);
   Stmt.setRemove admins (fun s => s⟦v⟧))
  [* fun t => t⟦u⟧ = t⟦v⟧ ∧ t⟦admins⟧ (t⟦u⟧) = false *]

/-- Catalog set example "wrong set operator", for an arbitrary one-element `teamA`. -/
def A08 : Prop := ∀ r : Ref,
  [* fun s => s⟦teamA⟧ = SetV.insert (a := .ref) r SetV.empty ∧ s⟦teamB⟧ = SetV.empty *]
  (Stmt.assign members (fun s => SetV.inter (s⟦teamA⟧) (s⟦teamB⟧)))
  [* fun t => t⟦teamA⟧ = SetV.insert (a := .ref) r SetV.empty ∧ t⟦teamB⟧ = SetV.empty ∧
              t⟦members⟧ = SetV.empty *]

/-- Catalog set example "marking a node visited", for an arbitrary `curr`. -/
def A09 : Prop :=
  [* fun s => s⟦visited⟧ (s⟦curr⟧) = false *]
  (Stmt.mapUpdate visited (fun s => s⟦curr⟧) (fun _ => true))
  [* fun t => t⟦visited⟧ (t⟦curr⟧) = true *]

/-- Catalog example "allocation alone", for an arbitrary free non-NULL node. -/
def A10 : Prop := ∀ r : Ref, r ≠ Ref.null →
  [* fun s => s.alloc r = false *]
  (Stmt.alloc n)
  [* fun t => t⟦n⟧ = r ∧ t.alloc r = true *]

/-- Catalog relation example "undirected edge removal, copy-paste bug", for two arbitrary distinct nodes. -/
def A11 : Prop :=
  [* fun s => s⟦u⟧ ≠ s⟦v⟧ ∧ s⟦adj⟧ (s⟦u⟧) (s⟦v⟧) = true ∧ s⟦adj⟧ (s⟦v⟧) (s⟦u⟧) = true *]
  (Stmt.relRemove adj (fun s => s⟦u⟧) (fun s => s⟦v⟧);
   Stmt.relRemove adj (fun s => s⟦u⟧) (fun s => s⟦v⟧))
  [* fun t => t⟦u⟧ ≠ t⟦v⟧ ∧ t⟦adj⟧ (t⟦u⟧) (t⟦v⟧) = false ∧ t⟦adj⟧ (t⟦v⟧) (t⟦u⟧) = true *]

/-- Catalog relation example "composition in the wrong order", for arbitrary ids with `p ≠ r`. -/
def A12 : Prop := ∀ p q r : Nat, p ≠ r →
  [* fun s => s⟦userRole⟧ = RelV.insert (a := .nat) (b := .nat) p q RelV.empty ∧
              s⟦rolePerm⟧ = RelV.insert (a := .nat) (b := .nat) q r RelV.empty *]
  (Stmt.assign userPerm (fun s => RelV.comp (s⟦rolePerm⟧) (s⟦userRole⟧)))
  [* fun t => t⟦userRole⟧ = RelV.insert (a := .nat) (b := .nat) p q RelV.empty ∧
              t⟦rolePerm⟧ = RelV.insert (a := .nat) (b := .nat) q r RelV.empty ∧
              t⟦userPerm⟧ = RelV.empty *]

/-- Catalog relation example "mutual follows with `∪` instead of `∩`", for two arbitrary distinct users. -/
def A13 : Prop := ∀ p q : Nat, p ≠ q →
  [* fun s => s⟦follows⟧ = RelV.insert (a := .nat) (b := .nat) p q RelV.empty *]
  (Stmt.assign mutualFollow (fun s => RelV.union (s⟦follows⟧) (RelV.inv (s⟦follows⟧))))
  [* fun t => t⟦follows⟧ = RelV.insert (a := .nat) (b := .nat) p q RelV.empty ∧
              t⟦mutualFollow⟧ = RelV.insert (a := .nat) (b := .nat) p q
                                  (RelV.insert q p RelV.empty) *]

-- =============================================================
-- B — loops, symbolic values, bounded iteration count
-- =============================================================

/-- Catalog Example 5 (loop guard `≤ 3`): from any start value `k ≤ 3` the loop ends with `x = 4`. -/
def B01 : Prop := ∀ k : Nat, k ≤ 3 →
  [* fun s => s⟦x⟧ = k *]
  (Stmt.whileDo (fun s => s⟦x⟧ ≤ 3)
    (Stmt.assign x (fun s => s⟦x⟧ + 1)))
  [* fun t => t⟦x⟧ = 4 *]

/-- Catalog Example 6 (one extra iteration): from any start value the counter ends at 6. -/
def B02 : Prop := ∀ k : Nat, k ≤ 6 →
  [* fun s => s⟦counter⟧ = k *]
  (Stmt.whileDo (fun s => s⟦counter⟧ < 6)
    (Stmt.assign counter (fun s => s⟦counter⟧ + 1)))
  [* fun t => t⟦counter⟧ = 6 *]

/-- Catalog Example 8 (rate limiter): from any start value the request counter ends at 5. -/
def B03 : Prop := ∀ k : Nat, k ≤ 5 →
  [* fun s => s⟦requests⟧ = k *]
  (Stmt.whileDo (fun s => s⟦requests⟧ < 5)
    (Stmt.assign requests (fun s => s⟦requests⟧ + 1)))
  [* fun t => t⟦requests⟧ = 5 *]

/-- Catalog Example 10 (loop changes `y`): `y` grows by 2 from an arbitrary start value. -/
def B04 : Prop := ∀ y₀ : Nat,
  [* fun s => s⟦x⟧ = 0 ∧ s⟦y⟧ = y₀ *]
  (Stmt.whileDo (fun s => s⟦x⟧ < 2)
    (Stmt.assign x (fun s => s⟦x⟧ + 1);
     Stmt.assign y (fun s => s⟦y⟧ + 1)))
  [* fun t => t⟦x⟧ = 2 ∧ t⟦y⟧ = y₀ + 2 *]

/-- Catalog Example 11 (sorted-array insert, two loops), values given only by order constraints. -/
def B05 : Prop :=
  [* fun s => s⟦a⟧ 0 < s⟦target⟧ ∧ s⟦a⟧ 1 = s⟦target⟧ ∧ s⟦a⟧ 2 > s⟦target⟧ ∧
              s⟦len⟧ = 3 ∧ s⟦i⟧ = 0 ∧ s⟦pos⟧ = 3 *]
  (Stmt.whileDo (fun s => s⟦i⟧ < 3 ∧ s⟦pos⟧ = 3)
     (Stmt.ifThenElse (fun s => s⟦a⟧ (s⟦i⟧) > s⟦target⟧)
         (Stmt.assign pos (fun s => s⟦i⟧)) Stmt.skip;
      Stmt.assign i (fun s => s⟦i⟧ + 1));
   Stmt.assign j (fun s => s⟦len⟧);
   Stmt.whileDo (fun s => s⟦j⟧ > s⟦pos⟧)
     (Stmt.mapUpdate a (fun s => s⟦j⟧) (fun s => s⟦a⟧ (s⟦j⟧ - 1));
      Stmt.assign j (fun s => s⟦j⟧ - 1));
   Stmt.mapUpdate a (fun s => s⟦pos⟧) (fun s => s⟦target⟧);
   Stmt.assign len (fun s => s⟦len⟧ + 1))
  [* fun t => t⟦a⟧ 0 < t⟦target⟧ ∧ t⟦a⟧ 1 = t⟦target⟧ ∧ t⟦a⟧ 2 = t⟦target⟧ ∧
              t⟦a⟧ 3 > t⟦target⟧ ∧ t⟦len⟧ = 4 ∧ t⟦i⟧ = 3 ∧ t⟦pos⟧ = 2 ∧ t⟦j⟧ = 2 *]

/-- Catalog Example 12 (linked-list insert), keys given only by constraints. -/
def B06 : Prop :=
  [* fun s =>
      s⟦head⟧ = ⟨1⟩ ∧ s⟦key⟧ ⟨1⟩ < s⟦target⟧ ∧ s⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧
      s⟦key⟧ ⟨2⟩ = s⟦target⟧ ∧ s⟦next⟧ ⟨2⟩ = Ref.null ∧
      s⟦prev⟧ = Ref.null ∧ s⟦curr⟧ = ⟨1⟩ ∧ s.alloc ⟨3⟩ = false *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) ≤ s⟦target⟧)
     (Stmt.assign prev (fun s => s⟦curr⟧);
      Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧)));
   Stmt.ifThenElse (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) = s⟦target⟧)
     Stmt.skip
     (Stmt.alloc n;
      Stmt.mapUpdate key (fun s => s⟦n⟧) (fun s => s⟦target⟧);
      Stmt.mapUpdate next (fun s => s⟦n⟧) (fun s => s⟦curr⟧);
      Stmt.ifThenElse (fun s => s⟦prev⟧ = Ref.null)
        (Stmt.assign head (fun s => s⟦n⟧))
        (Stmt.mapUpdate next (fun s => s⟦prev⟧) (fun s => s⟦n⟧))))
  [* fun t =>
      t⟦head⟧ = ⟨1⟩ ∧ t⟦key⟧ ⟨1⟩ < t⟦target⟧ ∧ t⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧
      t⟦key⟧ ⟨2⟩ = t⟦target⟧ ∧ t⟦next⟧ ⟨2⟩ = ⟨3⟩ ∧
      t⟦key⟧ ⟨3⟩ = t⟦target⟧ ∧ t⟦next⟧ ⟨3⟩ = Ref.null ∧
      t⟦prev⟧ = ⟨2⟩ ∧ t⟦curr⟧ = Ref.null ∧ t⟦n⟧ = ⟨3⟩ ∧ t.alloc ⟨3⟩ = true *]

/-- Catalog Example 12, correct `<` version (contrast): the list is left unchanged. -/
def B07 : Prop :=
  [* fun s =>
      s⟦head⟧ = ⟨1⟩ ∧ s⟦key⟧ ⟨1⟩ < s⟦target⟧ ∧ s⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧
      s⟦key⟧ ⟨2⟩ = s⟦target⟧ ∧ s⟦next⟧ ⟨2⟩ = Ref.null ∧
      s⟦prev⟧ = Ref.null ∧ s⟦curr⟧ = ⟨1⟩ ∧ s.alloc ⟨3⟩ = false *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) < s⟦target⟧)
     (Stmt.assign prev (fun s => s⟦curr⟧);
      Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧)));
   Stmt.ifThenElse (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) = s⟦target⟧)
     Stmt.skip
     (Stmt.alloc n;
      Stmt.mapUpdate key (fun s => s⟦n⟧) (fun s => s⟦target⟧);
      Stmt.mapUpdate next (fun s => s⟦n⟧) (fun s => s⟦curr⟧);
      Stmt.ifThenElse (fun s => s⟦prev⟧ = Ref.null)
        (Stmt.assign head (fun s => s⟦n⟧))
        (Stmt.mapUpdate next (fun s => s⟦prev⟧) (fun s => s⟦n⟧))))
  [* fun t =>
      t⟦head⟧ = ⟨1⟩ ∧ t⟦key⟧ ⟨1⟩ < t⟦target⟧ ∧ t⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧
      t⟦key⟧ ⟨2⟩ = t⟦target⟧ ∧ t⟦next⟧ ⟨2⟩ = Ref.null ∧
      t⟦prev⟧ = ⟨1⟩ ∧ t⟦curr⟧ = ⟨2⟩ ∧ t.alloc ⟨3⟩ = false *]

/-- Catalog Example 14 (sorted-array position search), values given only by constraints. -/
def B08 : Prop :=
  [* fun s => s⟦a⟧ 0 < s⟦target⟧ ∧ s⟦a⟧ 1 = s⟦target⟧ ∧ s⟦a⟧ 2 > s⟦target⟧ ∧
              s⟦i⟧ = 0 ∧ s⟦pos⟧ = 3 *]
  (Stmt.whileDo (fun s => s⟦i⟧ < 3 ∧ s⟦pos⟧ = 3)
    (Stmt.ifThenElse (fun s => s⟦a⟧ (s⟦i⟧) > s⟦target⟧)
        (Stmt.assign pos (fun s => s⟦i⟧)) Stmt.skip;
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦a⟧ 0 < t⟦target⟧ ∧ t⟦a⟧ 1 = t⟦target⟧ ∧ t⟦a⟧ 2 > t⟦target⟧ ∧
              t⟦i⟧ = 3 ∧ t⟦pos⟧ = 2 *]

/-- Catalog Example 15 (linked-list scan), keys given only by constraints. -/
def B09 : Prop :=
  [* fun s => s⟦key⟧ ⟨1⟩ < s⟦target⟧ ∧ s⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧
              s⟦key⟧ ⟨2⟩ = s⟦target⟧ ∧ s⟦next⟧ ⟨2⟩ = Ref.null ∧
              s⟦prev⟧ = Ref.null ∧ s⟦curr⟧ = ⟨1⟩ *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) ≤ s⟦target⟧)
    (Stmt.assign prev (fun s => s⟦curr⟧);
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧))))
  [* fun t => t⟦key⟧ ⟨1⟩ < t⟦target⟧ ∧ t⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧
              t⟦key⟧ ⟨2⟩ = t⟦target⟧ ∧ t⟦next⟧ ⟨2⟩ = Ref.null ∧
              t⟦prev⟧ = ⟨2⟩ ∧ t⟦curr⟧ = Ref.null *]

/-- Catalog set example "set updates inside a loop", with two arbitrary distinct node addresses. -/
def B10 : Prop := ∀ p q : Ref, p ≠ q → p ≠ Ref.null → q ≠ Ref.null →
  [* fun s => s⟦next⟧ p = q ∧ s⟦next⟧ q = Ref.null ∧ s⟦curr⟧ = p ∧
              s⟦visited⟧ Ref.null = false ∧ s⟦visited⟧ p = false ∧ s⟦visited⟧ q = false *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null)
    (Stmt.setInsert visited (fun s => s⟦next⟧ (s⟦curr⟧));
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧))))
  [* fun t => t⟦next⟧ p = q ∧ t⟦next⟧ q = Ref.null ∧ t⟦curr⟧ = Ref.null ∧
              t⟦visited⟧ Ref.null = true ∧ t⟦visited⟧ p = false ∧ t⟦visited⟧ q = true *]

/-- Catalog relation example "loading a directed graph with reversed edges", with three arbitrary distinct nodes. -/
def B11 : Prop := ∀ p q r : Ref, p ≠ q → q ≠ r → p ≠ r →
  [* fun s => s⟦src⟧ 0 = p ∧ s⟦dst⟧ 0 = q ∧ s⟦src⟧ 1 = q ∧ s⟦dst⟧ 1 = r ∧
              s⟦N⟧ = 2 ∧ s⟦i⟧ = 0 ∧
              s⟦E⟧ p q = false ∧ s⟦E⟧ q p = false ∧ s⟦E⟧ q r = false ∧ s⟦E⟧ r q = false *]
  (Stmt.whileDo (fun s => s⟦i⟧ < s⟦N⟧)
    (Stmt.relInsert E (fun s => s⟦dst⟧ (s⟦i⟧)) (fun s => s⟦src⟧ (s⟦i⟧));
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦src⟧ 0 = p ∧ t⟦dst⟧ 0 = q ∧ t⟦src⟧ 1 = q ∧ t⟦dst⟧ 1 = r ∧
              t⟦N⟧ = 2 ∧ t⟦i⟧ = 2 ∧
              t⟦E⟧ p q = false ∧ t⟦E⟧ q p = true ∧ t⟦E⟧ q r = false ∧ t⟦E⟧ r q = true *]

-- =============================================================
-- C — loops, arbitrary size (only an invariant / intermediate assertion may be given)
-- =============================================================

/-- Catalog Example 5 with an arbitrary bound `N`: because of `≤`, the loop ends at `N + 1`. -/
def C01 : Prop :=
  [* fun s => s⟦x⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦x⟧ ≤ s⟦N⟧)
    (Stmt.assign x (fun s => s⟦x⟧ + 1)))
  [* fun t => t⟦x⟧ = t⟦N⟧ + 1 *]

/-- Catalog Example 6 with an arbitrary bound `N`. -/
def C02 : Prop :=
  [* fun s => s⟦counter⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦counter⟧ < s⟦N⟧)
    (Stmt.assign counter (fun s => s⟦counter⟧ + 1)))
  [* fun t => t⟦counter⟧ = t⟦N⟧ *]

/-- Catalog Example 8 with an arbitrary bound `N`. -/
def C03 : Prop :=
  [* fun s => s⟦requests⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦requests⟧ < s⟦N⟧)
    (Stmt.assign requests (fun s => s⟦requests⟧ + 1)))
  [* fun t => t⟦requests⟧ = t⟦N⟧ *]

/-- Catalog Example 10 with an arbitrary bound `N`: `y` also ends at `N` (it should stay 0). -/
def C04 : Prop :=
  [* fun s => s⟦x⟧ = 0 ∧ s⟦y⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦x⟧ < s⟦N⟧)
    (Stmt.assign x (fun s => s⟦x⟧ + 1);
     Stmt.assign y (fun s => s⟦y⟧ + 1)))
  [* fun t => t⟦x⟧ = t⟦N⟧ ∧ t⟦y⟧ = t⟦N⟧ *]

/-- Catalog Example 11 on an array of arbitrary length (two loops). `target` is at position `k`; the buggy `>` inserts a second copy at position `k + 1`. -/
def C05 : Prop := ∀ k L : Nat,
  [* fun s => s⟦len⟧ = L ∧ k + 1 < L ∧ s⟦i⟧ = 0 ∧ s⟦pos⟧ = L ∧
      (∀ m, m < k → s⟦a⟧ m < s⟦target⟧) ∧ s⟦a⟧ k = s⟦target⟧ ∧
      (∀ m, k < m → m < L → s⟦a⟧ m > s⟦target⟧) *]
  (Stmt.whileDo (fun s => s⟦i⟧ < s⟦len⟧ ∧ s⟦pos⟧ = s⟦len⟧)
     (Stmt.ifThenElse (fun s => s⟦a⟧ (s⟦i⟧) > s⟦target⟧)
         (Stmt.assign pos (fun s => s⟦i⟧)) Stmt.skip;
      Stmt.assign i (fun s => s⟦i⟧ + 1));
   Stmt.assign j (fun s => s⟦len⟧);
   Stmt.whileDo (fun s => s⟦j⟧ > s⟦pos⟧)
     (Stmt.mapUpdate a (fun s => s⟦j⟧) (fun s => s⟦a⟧ (s⟦j⟧ - 1));
      Stmt.assign j (fun s => s⟦j⟧ - 1));
   Stmt.mapUpdate a (fun s => s⟦pos⟧) (fun s => s⟦target⟧);
   Stmt.assign len (fun s => s⟦len⟧ + 1))
  [* fun t => t⟦len⟧ = L + 1 ∧ k + 1 < L ∧ t⟦i⟧ = k + 2 ∧ t⟦pos⟧ = k + 1 ∧ t⟦j⟧ = k + 1 ∧
      (∀ m, m < k → t⟦a⟧ m < t⟦target⟧) ∧ t⟦a⟧ k = t⟦target⟧ ∧ t⟦a⟧ (k + 1) = t⟦target⟧ ∧
      (∀ m, k + 2 ≤ m → m ≤ L → t⟦a⟧ m > t⟦target⟧) *]

/-- The advisor's example: linked-list insert on a list of arbitrary length (the triple of `LinkedList.lean`, today proved by hand). -/
def C06 : Prop := ∀ yv : Nat,
  [* LinkedList.hasKey yv *] (LinkedList.insertProg) [* LinkedList.PostAny yv *]

/-- Catalog Example 13 (walking past the tail of a list of arbitrary length); same statement as in the catalog. -/
def C07 : Prop :=
  [* fun s => s⟦curr⟧ = ⟨1⟩ ∧ s⟦prev⟧ = Ref.null ∧ s⟦i⟧ = 1 ∧ 1 ≤ s⟦N⟧ ∧
      ∀ k, 1 ≤ k → k ≤ s⟦N⟧ → s⟦next⟧ ⟨k⟩ = if k + 1 ≤ s⟦N⟧ then ⟨k + 1⟩ else Ref.null *]
  (Stmt.whileDo (fun s => s⟦i⟧ ≤ s⟦N⟧)
    (Stmt.assign prev (fun s => s⟦curr⟧);
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧));
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦curr⟧ = Ref.null ∧ t⟦prev⟧ = ⟨t⟦N⟧⟩ ∧ t⟦i⟧ = t⟦N⟧ + 1 ∧ 1 ≤ t⟦N⟧ ∧
      ∀ k, 1 ≤ k → k ≤ t⟦N⟧ → t⟦next⟧ ⟨k⟩ = if k + 1 ≤ t⟦N⟧ then ⟨k + 1⟩ else Ref.null *]

/-- Catalog Example 14 on an array of arbitrary length: `target` is at position `k` and later cells are larger; the buggy `>` gives `pos = k + 1` instead of `k`. -/
def C08 : Prop := ∀ k : Nat,
  [* fun s => s⟦len⟧ = s⟦N⟧ ∧ k + 1 < s⟦N⟧ ∧ s⟦i⟧ = 0 ∧ s⟦pos⟧ = s⟦N⟧ ∧
      (∀ m, m < k → s⟦a⟧ m < s⟦target⟧) ∧ s⟦a⟧ k = s⟦target⟧ ∧
      (∀ m, k < m → m < s⟦N⟧ → s⟦a⟧ m > s⟦target⟧) *]
  (Stmt.whileDo (fun s => s⟦i⟧ < s⟦len⟧ ∧ s⟦pos⟧ = s⟦len⟧)
    (Stmt.ifThenElse (fun s => s⟦a⟧ (s⟦i⟧) > s⟦target⟧)
        (Stmt.assign pos (fun s => s⟦i⟧)) Stmt.skip;
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦len⟧ = t⟦N⟧ ∧ k + 1 < t⟦N⟧ ∧ t⟦i⟧ = k + 2 ∧ t⟦pos⟧ = k + 1 ∧
      (∀ m, m < k → t⟦a⟧ m < t⟦target⟧) ∧ t⟦a⟧ k = t⟦target⟧ ∧
      (∀ m, k < m → m < t⟦N⟧ → t⟦a⟧ m > t⟦target⟧) *]

/-- Catalog Example 15 on a list ⟨1⟩ → … → ⟨N⟩ of arbitrary length, key of node m is m, target is the last key; because of `≤` the scan falls off the end. -/
def C09 : Prop :=
  [* fun s => s⟦curr⟧ = ⟨1⟩ ∧ s⟦prev⟧ = Ref.null ∧ 1 ≤ s⟦N⟧ ∧ s⟦target⟧ = s⟦N⟧ ∧
      (∀ m, 1 ≤ m → m ≤ s⟦N⟧ → s⟦key⟧ ⟨m⟩ = m) ∧
      (∀ m, 1 ≤ m → m ≤ s⟦N⟧ → s⟦next⟧ ⟨m⟩ = if m + 1 ≤ s⟦N⟧ then ⟨m + 1⟩ else Ref.null) *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) ≤ s⟦target⟧)
    (Stmt.assign prev (fun s => s⟦curr⟧);
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧))))
  [* fun t => t⟦curr⟧ = Ref.null ∧ t⟦prev⟧ = ⟨t⟦N⟧⟩ ∧ 1 ≤ t⟦N⟧ ∧ t⟦target⟧ = t⟦N⟧ ∧
      (∀ m, 1 ≤ m → m ≤ t⟦N⟧ → t⟦key⟧ ⟨m⟩ = m) ∧
      (∀ m, 1 ≤ m → m ≤ t⟦N⟧ → t⟦next⟧ ⟨m⟩ = if m + 1 ≤ t⟦N⟧ then ⟨m + 1⟩ else Ref.null) *]

/-- Catalog set example "set updates inside a loop" on a list of arbitrary length: since `next[curr]` is marked, the head is never marked and NULL is. -/
def C10 : Prop :=
  [* fun s => s⟦curr⟧ = ⟨1⟩ ∧ 1 ≤ s⟦N⟧ ∧
      (∀ m, 1 ≤ m → m ≤ s⟦N⟧ → s⟦next⟧ ⟨m⟩ = if m + 1 ≤ s⟦N⟧ then ⟨m + 1⟩ else Ref.null) ∧
      (∀ m, m ≤ s⟦N⟧ → s⟦visited⟧ ⟨m⟩ = false) *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null)
    (Stmt.setInsert visited (fun s => s⟦next⟧ (s⟦curr⟧));
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧))))
  [* fun t => t⟦curr⟧ = Ref.null ∧ 1 ≤ t⟦N⟧ ∧
      (∀ m, 1 ≤ m → m ≤ t⟦N⟧ → t⟦next⟧ ⟨m⟩ = if m + 1 ≤ t⟦N⟧ then ⟨m + 1⟩ else Ref.null) ∧
      t⟦visited⟧ Ref.null = true ∧ t⟦visited⟧ ⟨1⟩ = false ∧
      (∀ m, 2 ≤ m → m ≤ t⟦N⟧ → t⟦visited⟧ ⟨m⟩ = true) *]

/-- Catalog relation example "reversed edges" on a path of arbitrary length (N edges). -/
def C11 : Prop :=
  [* fun s => s⟦i⟧ = 0 ∧
      (∀ m, m < s⟦N⟧ → s⟦src⟧ m = ⟨m + 1⟩ ∧ s⟦dst⟧ m = ⟨m + 2⟩) ∧
      (∀ m, m < s⟦N⟧ → s⟦E⟧ ⟨m + 1⟩ ⟨m + 2⟩ = false ∧ s⟦E⟧ ⟨m + 2⟩ ⟨m + 1⟩ = false) *]
  (Stmt.whileDo (fun s => s⟦i⟧ < s⟦N⟧)
    (Stmt.relInsert E (fun s => s⟦dst⟧ (s⟦i⟧)) (fun s => s⟦src⟧ (s⟦i⟧));
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦i⟧ = t⟦N⟧ ∧
      (∀ m, m < t⟦N⟧ → t⟦src⟧ m = ⟨m + 1⟩ ∧ t⟦dst⟧ m = ⟨m + 2⟩) ∧
      (∀ m, m < t⟦N⟧ → t⟦E⟧ ⟨m + 1⟩ ⟨m + 2⟩ = false ∧ t⟦E⟧ ⟨m + 2⟩ ⟨m + 1⟩ = true) *]

end MapLang.Examples
