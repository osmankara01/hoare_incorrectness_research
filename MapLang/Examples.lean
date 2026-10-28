import MapLang.VCGen

/-!
# Example catalogue in MapLang

The bug catalogue of `Incorrectness/RealWorldExamples.lean` (Examples 1–15),
re-done in the map language, plus bugs in set and relation code.  What the
new language changes for the *user*:

* **No more per-node variable names.**  The old encoding needed `key_1`,
  `next_2`, `a0`, `a1`, … as separate scalar variables and simprocs to read
  them.  Here `key`, `next`, `a` are single map-valued variables and
  `s⟦key⟧ n`, `s⟦a⟧ i` are genuine applications.
* **Typed pointer variables.**  `curr`, `prev`, `head`, `n` are `Var .ref`;
  the guard `s⟦curr⟧ ≠ Ref.null` is a comparison of addresses, not of `Nat`s.
* **Real allocation and real field writes.**  `Stmt.alloc n` is `n := new`,
  `Stmt.mapUpdate next (·⟦prev⟧) (·⟦n⟧)` is `next[prev] := n`.
* **Sets.**  A `Var (.set .ref)` is a set of nodes.  Point updates have their
  own statements with their own big-step rules (`Stmt.setInsert`,
  `Stmt.setRemove`); whole-set expressions (`SetV.union`, `SetV.inter`,
  `SetV.diff`, `SetV.empty`, …) are used inside `Stmt.assign`.
* **Relations.**  A `Var (.rel a b)` is a binary relation.  Pair updates have
  their own statements (`Stmt.relInsert`, `Stmt.relRemove`); whole-relation
  expressions (`RelV.empty`, `RelV.union`, `RelV.inv` (converse),
  `RelV.comp` (composition), …) are used inside `Stmt.assign`.

## How the examples are closed

Every example is closed by ONE tactic call.  All of them except Example 13
use `incorrectness_auto` with no argument at all:

1. A loop-free program goes through `vc_sound` and the strongest
   postcondition `sp`.
2. Otherwise the tactic tries the depths `k = 0, 1, …, 10`: `unrollAll k`
   replaces EVERY loop of the program (also a loop in the middle of a
   sequence, such as a scan followed by a splice) by its `k`-fold unrolling.
   This is sound for IL because IL under-approximates: a state reached by
   the unrolled program is reached by the original one (`vc_unroll_sound`).
   A depth that is too small simplifies to `False` and the search moves on.
3. The existentials over old values that `sp` introduces are eliminated by
   the simproc `existsPin` wherever a pinning equation `v = c` occurs.

Example 13 has a SYMBOLIC iteration count (a list of arbitrary length `N`),
which no finite unrolling covers.  It is closed by `incorrectness_auto_inv`
with a hand-written indexed invariant; that invariant is the only
proof-specific input in this file.

| #  | Bug                                                        | Loops | Proof |
|----|------------------------------------------------------------|-------|-------|
| 1  | `<` vs `≤` in a withdrawal check                           | 0 | `incorrectness_auto` |
| 2  | `≥` vs `>` in a discount threshold                         | 0 | `incorrectness_auto` |
| 3  | `>` vs `≥` in an age check                                 | 0 | `incorrectness_auto` |
| 4  | `∨` vs `∧` in access control                               | 0 | `incorrectness_auto` |
| 5  | loop guard `≤ 3` vs `< 3`                                  | 1 | `incorrectness_auto` |
| 6  | loop bound 6 instead of 5                                  | 1 | `incorrectness_auto` |
| 7  | `≥` vs `>` in a request validator                          | 0 | `incorrectness_auto` |
| 8  | rate limiter bound 5 instead of 3                          | 1 | `incorrectness_auto` |
| 9  | assertion too weak, misses a case                          | 0 | `incorrectness_auto` |
| 10 | loop body also changes a variable it should not            | 1 | `incorrectness_auto` |
| 11 | sorted-array insert: `>` vs `≥` scan, then a shift loop    | 2 | `incorrectness_auto` |
| 12 | linked-list insert: `≤` scan, dup check, `new`, splice     | 1 | `incorrectness_auto` |
| 13 | linked-list walk past the tail, list of symbolic length N  | 1 | `incorrectness_auto_inv inv` |
| 14 | sorted-array position search, `>` vs `≥`                   | 1 | `incorrectness_auto` |
| 15 | linked-list position scan, `≤` vs `<`                      | 1 | `incorrectness_auto` |
| —  | set aliasing, wrong set operator, set update in a loop     | 0–1 | `incorrectness_auto` |
| —  | four relation bugs (one in a loop)                         | 0–1 | `incorrectness_auto` |

**Limits.**  Apart from Example 13 the inputs are concrete (fixed lists and
arrays), and unrolling covers at most 10 iterations per loop.  The
arbitrary-list version of Example 12 (the advisor's specification) lives in
`MapLang/LinkedList.lean` and is proved by hand, not by these tactics.
-/

namespace MapLang.Examples

-- ------------------------------------------------------------
-- Program variables used across the examples
-- ------------------------------------------------------------

def balance    : Var .nat := ⟨"balance"⟩
def withdrawal : Var .nat := ⟨"withdrawal"⟩
def approved   : Var .nat := ⟨"approved"⟩
def amount     : Var .nat := ⟨"amount"⟩
def discounted : Var .nat := ⟨"discounted"⟩
def age        : Var .nat := ⟨"age"⟩
def allowed    : Var .nat := ⟨"allowed"⟩
def admin      : Var .nat := ⟨"admin"⟩
def active     : Var .nat := ⟨"active"⟩
def access     : Var .nat := ⟨"access"⟩
def counter    : Var .nat := ⟨"counter"⟩
def input      : Var .nat := ⟨"input"⟩
def result     : Var .nat := ⟨"result"⟩
def requests   : Var .nat := ⟨"requests"⟩
def x      : Var .nat := ⟨"x"⟩
def y      : Var .nat := ⟨"y"⟩
def N      : Var .nat := ⟨"N"⟩
def i      : Var .nat := ⟨"i"⟩
def j      : Var .nat := ⟨"j"⟩
def pos    : Var .nat := ⟨"pos"⟩
def len    : Var .nat := ⟨"len"⟩
def target : Var .nat := ⟨"target"⟩
/-- An array is a map `nat ⇒ nat`. -/
def a      : Var (.map .nat .nat) := ⟨"a"⟩
def head   : Var .ref := ⟨"head"⟩
def curr   : Var .ref := ⟨"curr"⟩
def prev   : Var .ref := ⟨"prev"⟩
def n      : Var .ref := ⟨"n"⟩
/-- `key : Node → Nat`. -/
def key    : Var (.map .ref .nat) := ⟨"key"⟩
/-- `next : Node → Node`. -/
def next   : Var (.map .ref .ref) := ⟨"next"⟩
/-- A set of nodes is a map `ref ⇒ bool`. -/
def visited : Var (.set .ref) := ⟨"visited"⟩
def admins  : Var (.set .ref) := ⟨"admins"⟩
def teamA   : Var (.set .ref) := ⟨"teamA"⟩
def teamB   : Var (.set .ref) := ⟨"teamB"⟩
def members : Var (.set .ref) := ⟨"members"⟩
def u       : Var .ref := ⟨"u"⟩
def v       : Var .ref := ⟨"v"⟩
/-- A binary relation on nodes (directed edges) is a map `ref ⇒ ref ⇒ bool`. -/
def E       : Var (.rel .ref .ref) := ⟨"E"⟩
def adj     : Var (.rel .ref .ref) := ⟨"adj"⟩
/-- Edge lists as two parallel arrays of nodes (`nat ⇒ ref`). -/
def src     : Var (.map .nat .ref) := ⟨"src"⟩
def dst     : Var (.map .nat .ref) := ⟨"dst"⟩
def userRole : Var (.rel .nat .nat) := ⟨"userRole"⟩
def rolePerm : Var (.rel .nat .nat) := ⟨"rolePerm"⟩
def userPerm : Var (.rel .nat .nat) := ⟨"userPerm"⟩
def follows  : Var (.rel .nat .nat) := ⟨"follows"⟩
def mutualFollow : Var (.rel .nat .nat) := ⟨"mutualFollow"⟩

-- =============================================================
-- Example 1 — bank withdrawal: `<` instead of `≤`
-- =============================================================
/-- A withdrawal must be approved whenever it does not exceed the balance.
    The buggy strict `<` rejects a withdrawal equal to the balance
    (balance 100, withdrawal 100). -/
example :
  [* fun s => s⟦balance⟧ = 100 ∧ s⟦withdrawal⟧ = 100 *]
  (Stmt.ifThenElse (fun s => s⟦withdrawal⟧ < s⟦balance⟧)          -- BUG: should be ≤
    (Stmt.assign approved (fun _ => 1))
    (Stmt.assign approved (fun _ => 0)))
  [* fun t => t⟦approved⟧ = 0 ∧ t⟦balance⟧ = 100 ∧ t⟦withdrawal⟧ = 100 *] := by
  incorrectness_auto

-- =============================================================
-- Example 2 — discount threshold: `≥` instead of `>`
-- =============================================================
/-- "10% discount for orders over 1000": the buggy `≥` also discounts an
    order of exactly 1000. -/
example :
  [* fun s => s⟦amount⟧ = 1000 *]
  (Stmt.ifThenElse (fun s => s⟦amount⟧ ≥ 1000)                    -- BUG: should be >
    (Stmt.assign discounted (fun _ => 1))
    (Stmt.assign discounted (fun _ => 0)))
  [* fun t => t⟦discounted⟧ = 1 ∧ t⟦amount⟧ = 1000 *] := by
  incorrectness_auto

-- =============================================================
-- Example 3 — age check: `>` instead of `≥`
-- =============================================================
/-- The age gate should admit `age ≥ 18`; the buggy strict `>` rejects an
    18-year-old. -/
example :
  [* fun s => s⟦age⟧ = 18 *]
  (Stmt.ifThenElse (fun s => s⟦age⟧ > 18)                         -- BUG: should be ≥
    (Stmt.assign allowed (fun _ => 1))
    (Stmt.assign allowed (fun _ => 0)))
  [* fun t => t⟦allowed⟧ = 0 ∧ t⟦age⟧ = 18 *] := by
  incorrectness_auto

-- =============================================================
-- Example 4 — access control: `∨` instead of `∧`
-- =============================================================
/-- Access should require admin AND active.  With the buggy OR, an active
    non-admin user gets access (privilege escalation). -/
example :
  [* fun s => s⟦admin⟧ = 0 ∧ s⟦active⟧ = 1 *]
  (Stmt.ifThenElse (fun s => s⟦admin⟧ = 1 ∨ s⟦active⟧ = 1)        -- BUG: should be ∧
    (Stmt.assign access (fun _ => 1))
    (Stmt.assign access (fun _ => 0)))
  [* fun t => t⟦access⟧ = 1 ∧ t⟦admin⟧ = 0 ∧ t⟦active⟧ = 1 *] := by
  incorrectness_auto

-- =============================================================
-- Example 5 — loop guard: `≤ 3` instead of `< 3`
-- =============================================================
/-- A loop meant to run 3 times runs 4 times and leaves `x = 4`. -/
example :
  [* fun s => s⟦x⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦x⟧ ≤ 3)                                 -- BUG: should be < 3
    (Stmt.assign x (fun s => s⟦x⟧ + 1)))
  [* fun t => t⟦x⟧ = 4 *] := by
  incorrectness_auto

-- =============================================================
-- Example 6 — loop runs one extra iteration
-- =============================================================
/-- The intended bound is 5, the buggy bound 6: the counter ends at 6. -/
example :
  [* fun s => s⟦counter⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦counter⟧ < 6)                           -- BUG: intended 5
    (Stmt.assign counter (fun s => s⟦counter⟧ + 1)))
  [* fun t => t⟦counter⟧ = 6 *] := by
  incorrectness_auto

-- =============================================================
-- Example 7 — request validator: `≥` instead of `>`
-- =============================================================
/-- Requests must exceed 50 to be approved; the buggy `≥` approves 50. -/
example :
  [* fun s => s⟦input⟧ = 50 *]
  (Stmt.ifThenElse (fun s => s⟦input⟧ ≥ 50)                       -- BUG: should be >
    (Stmt.assign result (fun _ => 1))                             -- approved
    (Stmt.assign result (fun _ => 0)))                            -- rejected
  [* fun t => t⟦result⟧ = 1 ∧ t⟦input⟧ = 50 *] := by
  incorrectness_auto

-- =============================================================
-- Example 8 — rate limiter with the wrong cap
-- =============================================================
/-- At most 3 requests should pass; the buggy cap lets the counter reach 5. -/
example :
  [* fun s => s⟦requests⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦requests⟧ < 5)                          -- BUG: intended 3
    (Stmt.assign requests (fun s => s⟦requests⟧ + 1)))
  [* fun t => t⟦requests⟧ = 5 *] := by
  incorrectness_auto

-- =============================================================
-- Example 9 — an assertion that misses a case
-- =============================================================
/-- The assertion only rules out `x = 0`, but the code below also mishandles
    `x = 1`: it passes the check and lands in the error branch (`999`). -/
example :
  [* fun s => s⟦x⟧ = 1 *]
  (Stmt.assert (fun s => s⟦x⟧ ≠ 0);                                 -- too weak
   Stmt.ifThenElse (fun s => s⟦x⟧ > 1)
     (Stmt.assign result (fun _ => 100))
     (Stmt.assign result (fun _ => 999)))                         -- error sentinel
  [* fun t => t⟦result⟧ = 999 ∧ t⟦x⟧ = 1 *] := by
  incorrectness_auto

-- =============================================================
-- Example 10 — loop body changes a variable it should not
-- =============================================================
/-- The loop should only advance `x`, but its body also increments `y`, so
    after two iterations `y = 2` instead of `0`. -/
example :
  [* fun s => s⟦x⟧ = 0 ∧ s⟦y⟧ = 0 *]
  (Stmt.whileDo (fun s => s⟦x⟧ < 2)
    (Stmt.assign x (fun s => s⟦x⟧ + 1);
     Stmt.assign y (fun s => s⟦y⟧ + 1)))                            -- BUG: y must not change
  [* fun t => t⟦x⟧ = 2 ∧ t⟦y⟧ = 2 *] := by
  incorrectness_auto

-- =============================================================
-- Example 11 — sorted-array insert with a REAL shift loop (`a[j] := a[j-1]`)
-- =============================================================
/-- Insert `target` into a sorted array: find the position, shift the tail
    right by one, write `target`.

      i := 0;
      while (i < 3 ∧ pos = 3) { if a[i] > target then pos := i; i := i + 1 }   -- BUG: > not ≥
      j := len;
      while (j > pos) { a[j] := a[j-1]; j := j - 1 };
      a[pos] := target; len := len + 1

    On `[1, 3, 5]` with target 3 the buggy scan overshoots to `pos = 2`, so the
    result is `[1, 3, 3, 5]` — a duplicate.  (The old encoding needed eight
    guarded slot writes for the shift; here it is one `mapUpdate` in a loop.)

    Proof: one `incorrectness_auto` call.  Both loops are unrolled together
    (depth 3), so no midpoint between the scan and the shift and no
    invariant is written.  This is the costliest example of the file
    (≈ 45 s). -/
example :
  [* fun s => s⟦a⟧ 0 = 1 ∧ s⟦a⟧ 1 = 3 ∧ s⟦a⟧ 2 = 5 ∧ s⟦len⟧ = 3 ∧ s⟦target⟧ = 3 ∧
              s⟦i⟧ = 0 ∧ s⟦pos⟧ = 3 *]
  (Stmt.whileDo (fun s => s⟦i⟧ < 3 ∧ s⟦pos⟧ = 3)
     (Stmt.ifThenElse (fun s => s⟦a⟧ (s⟦i⟧) > s⟦target⟧)            -- BUG: > should be ≥
         (Stmt.assign pos (fun s => s⟦i⟧)) Stmt.skip;
      Stmt.assign i (fun s => s⟦i⟧ + 1));
   Stmt.assign j (fun s => s⟦len⟧);
   Stmt.whileDo (fun s => s⟦j⟧ > s⟦pos⟧)
     (Stmt.mapUpdate a (fun s => s⟦j⟧) (fun s => s⟦a⟧ (s⟦j⟧ - 1));    -- a[j] := a[j-1]
      Stmt.assign j (fun s => s⟦j⟧ - 1));
   Stmt.mapUpdate a (fun s => s⟦pos⟧) (fun s => s⟦target⟧);          -- a[pos] := target
   Stmt.assign len (fun s => s⟦len⟧ + 1))
  [* fun t => t⟦a⟧ 0 = 1 ∧ t⟦a⟧ 1 = 3 ∧ t⟦a⟧ 2 = 3 ∧ t⟦a⟧ 3 = 5 ∧ t⟦len⟧ = 4 ∧ t⟦target⟧ = 3 ∧
              t⟦i⟧ = 3 ∧ t⟦pos⟧ = 2 ∧ t⟦j⟧ = 2 *] := by
  incorrectness_auto

-- =============================================================
-- Example 12 — linked-list insert on a concrete list: scan + new + splice
-- =============================================================
/-- The concrete (2-node) instance of the advisor's insert example.  Program
    (C++: `if (curr != NIL && key[curr] == target) return;` is the "already
    present?" check):

      while (curr ≠ NULL ∧ key[curr] ≤ target) { prev := curr; curr := next[curr] }
      if (curr ≠ NULL ∧ key[curr] = target) then skip
      else { n := new; key[n] := target; next[n] := curr;
             if prev = NULL then head := n else next[prev] := n }

    The list `⟨1⟩ (1) → ⟨2⟩ (3) → NULL` with target 3 becomes
    `⟨1⟩ (1) → ⟨2⟩ (3) → ⟨3⟩ (3) → NULL`: a duplicate key.  The buggy `≤`
    scan walks past the node holding 3, so at the check `curr = NULL` and the
    check cannot fire.

    Proof: one `incorrectness_auto` call; the scan loop is unrolled in place,
    in front of the check and the splice.  The arbitrary-list version of the
    same triple is `LinkedList.insert_triple_hasKey` (manual proof). -/
example :
  [* fun s =>
      s⟦head⟧ = ⟨1⟩ ∧ s⟦key⟧ ⟨1⟩ = 1 ∧ s⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ s⟦key⟧ ⟨2⟩ = 3 ∧ s⟦next⟧ ⟨2⟩ = Ref.null ∧
      s⟦target⟧ = 3 ∧ s⟦prev⟧ = Ref.null ∧ s⟦curr⟧ = ⟨1⟩ ∧ s.alloc ⟨3⟩ = false *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) ≤ s⟦target⟧)   -- BUG: ≤
     (Stmt.assign prev (fun s => s⟦curr⟧);
      Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧)));
   Stmt.ifThenElse (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) = s⟦target⟧)  -- present?
     Stmt.skip
     (Stmt.alloc n;
      Stmt.mapUpdate key (fun s => s⟦n⟧) (fun s => s⟦target⟧);
      Stmt.mapUpdate next (fun s => s⟦n⟧) (fun s => s⟦curr⟧);
      Stmt.ifThenElse (fun s => s⟦prev⟧ = Ref.null)
        (Stmt.assign head (fun s => s⟦n⟧))
        (Stmt.mapUpdate next (fun s => s⟦prev⟧) (fun s => s⟦n⟧))))
  [* fun t =>
      t⟦head⟧ = ⟨1⟩ ∧ t⟦key⟧ ⟨1⟩ = 1 ∧ t⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ t⟦key⟧ ⟨2⟩ = 3 ∧ t⟦next⟧ ⟨2⟩ = ⟨3⟩ ∧
      t⟦key⟧ ⟨3⟩ = 3 ∧ t⟦next⟧ ⟨3⟩ = Ref.null ∧
      t⟦target⟧ = 3 ∧ t⟦prev⟧ = ⟨2⟩ ∧ t⟦curr⟧ = Ref.null ∧ t⟦n⟧ = ⟨3⟩ ∧ t.alloc ⟨3⟩ = true *] := by
  incorrectness_auto

/-- **Contrast: the same program with the correct `<`.**  The scan now stops
    ON the node holding 3 (`curr = ⟨2⟩`), the "already present?" check fires
    and the list is left unchanged — node ⟨3⟩ is never allocated.

    Caveat: an IL triple only shows that this state is *reachable*.  That the
    corrected program *never* creates a duplicate is a correctness (Hoare)
    statement, which IL cannot express and which is not proved here. -/
example :
  [* fun s =>
      s⟦head⟧ = ⟨1⟩ ∧ s⟦key⟧ ⟨1⟩ = 1 ∧ s⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ s⟦key⟧ ⟨2⟩ = 3 ∧ s⟦next⟧ ⟨2⟩ = Ref.null ∧
      s⟦target⟧ = 3 ∧ s⟦prev⟧ = Ref.null ∧ s⟦curr⟧ = ⟨1⟩ ∧ s.alloc ⟨3⟩ = false *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) < s⟦target⟧)   -- correct: <
     (Stmt.assign prev (fun s => s⟦curr⟧);
      Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧)));
   Stmt.ifThenElse (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) = s⟦target⟧)  -- present?
     Stmt.skip
     (Stmt.alloc n;
      Stmt.mapUpdate key (fun s => s⟦n⟧) (fun s => s⟦target⟧);
      Stmt.mapUpdate next (fun s => s⟦n⟧) (fun s => s⟦curr⟧);
      Stmt.ifThenElse (fun s => s⟦prev⟧ = Ref.null)
        (Stmt.assign head (fun s => s⟦n⟧))
        (Stmt.mapUpdate next (fun s => s⟦prev⟧) (fun s => s⟦n⟧))))
  [* fun t =>
      t⟦head⟧ = ⟨1⟩ ∧ t⟦key⟧ ⟨1⟩ = 1 ∧ t⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ t⟦key⟧ ⟨2⟩ = 3 ∧ t⟦next⟧ ⟨2⟩ = Ref.null ∧
      t⟦target⟧ = 3 ∧ t⟦prev⟧ = ⟨1⟩ ∧ t⟦curr⟧ = ⟨2⟩ ∧ t.alloc ⟨3⟩ = false *] := by
  incorrectness_auto

-- =============================================================
-- Example 13 — walking past the tail of a list of SYMBOLIC length N
-- =============================================================
/-- A list of arbitrary length `N ≥ 1`: nodes `⟨1⟩ → ⟨2⟩ → … → ⟨N⟩ → NULL`,
    given by one universally quantified fact about the map `next`.  The code
    should stop ON the tail (e.g. to append after it), i.e. take `N - 1`
    steps.  C++:

      curr = head; prev = NULL;
      for (i = 1; i <= N; i++) { prev = curr; curr = next[curr]; }   // BUG: i < N

    With the buggy `≤` the walk takes one step too many: `curr` falls off the
    end (`NULL`) and `prev` is the tail `⟨N⟩` — for every `N`.

    The iteration count is symbolic, so no finite unrolling covers it; the
    proof is one `incorrectness_auto_inv` call with the indexed invariant
    "after `k` steps, `i = k + 1`, `prev` is node `k` (NULL for `k = 0`) and
    `curr` is node `k + 1`, or NULL once `k = N`". -/
example :
  [* fun s => s⟦curr⟧ = ⟨1⟩ ∧ s⟦prev⟧ = Ref.null ∧ s⟦i⟧ = 1 ∧ 1 ≤ s⟦N⟧ ∧
      ∀ k, 1 ≤ k → k ≤ s⟦N⟧ → s⟦next⟧ ⟨k⟩ = if k + 1 ≤ s⟦N⟧ then ⟨k + 1⟩ else Ref.null *]
  (Stmt.whileDo (fun s => s⟦i⟧ ≤ s⟦N⟧)                               -- BUG: should be <
    (Stmt.assign prev (fun s => s⟦curr⟧);
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧));
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦curr⟧ = Ref.null ∧ t⟦prev⟧ = ⟨t⟦N⟧⟩ ∧ t⟦i⟧ = t⟦N⟧ + 1 ∧ 1 ≤ t⟦N⟧ ∧
      ∀ k, 1 ≤ k → k ≤ t⟦N⟧ → t⟦next⟧ ⟨k⟩ = if k + 1 ≤ t⟦N⟧ then ⟨k + 1⟩ else Ref.null *] := by
  incorrectness_auto_inv (fun k s =>
    s⟦i⟧ = k + 1 ∧ k ≤ s⟦N⟧ ∧ 1 ≤ s⟦N⟧ ∧
    s⟦curr⟧ = (if k + 1 ≤ s⟦N⟧ then Ref.mk (k + 1) else Ref.null) ∧
    s⟦prev⟧ = (if k = 0 then Ref.null else Ref.mk k) ∧
    ∀ j, 1 ≤ j → j ≤ s⟦N⟧ → s⟦next⟧ ⟨j⟩ = if j + 1 ≤ s⟦N⟧ then ⟨j + 1⟩ else Ref.null)

-- =============================================================
-- Example 14 — sorted-array position search, `>` vs `≥`, genuine `a[i]`
-- =============================================================
/-- `a = [1, 3, 5]`, `target = 3`.  The scan tests `a[i] > target` where it
    should test `≥`, so it walks past the existing `3` and reports `pos = 2`
    instead of `1`.  The array is ONE map variable and `s⟦a⟧ (s⟦i⟧)` is real
    indexing (the old encoding needed a disjunction over `i = 0, 1, 2`).
    This is the scan phase of Example 11 on its own. -/
example :
  [* fun s => s⟦a⟧ 0 = 1 ∧ s⟦a⟧ 1 = 3 ∧ s⟦a⟧ 2 = 5 ∧
              s⟦target⟧ = 3 ∧ s⟦i⟧ = 0 ∧ s⟦pos⟧ = 3 *]
  (Stmt.whileDo (fun s => s⟦i⟧ < 3 ∧ s⟦pos⟧ = 3)
    (Stmt.ifThenElse (fun s => s⟦a⟧ (s⟦i⟧) > s⟦target⟧)             -- BUG: > should be ≥
        (Stmt.assign pos (fun s => s⟦i⟧)) Stmt.skip;
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦a⟧ 0 = 1 ∧ t⟦a⟧ 1 = 3 ∧ t⟦a⟧ 2 = 5 ∧
              t⟦target⟧ = 3 ∧ t⟦i⟧ = 3 ∧ t⟦pos⟧ = 2 *] := by
  incorrectness_auto

-- =============================================================
-- Example 15 — linked-list scan, `≤` vs `<`, with `key`/`next` maps
-- =============================================================
/-- List `⟨1⟩ (key 1) → ⟨2⟩ (key 3) → NULL`, target `3`.  The scan guard
    `key[curr] ≤ target` (should be `<`) advances past the node holding the
    target: `curr` runs off to NULL and `prev` stops on ⟨2⟩.  This is the
    scan phase of Example 12 on its own. -/
example :
  [* fun s => s⟦key⟧ ⟨1⟩ = 1 ∧ s⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ s⟦key⟧ ⟨2⟩ = 3 ∧ s⟦next⟧ ⟨2⟩ = Ref.null ∧
              s⟦target⟧ = 3 ∧ s⟦prev⟧ = Ref.null ∧ s⟦curr⟧ = ⟨1⟩ *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) ≤ s⟦target⟧)   -- BUG: ≤
    (Stmt.assign prev (fun s => s⟦curr⟧);
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧))))
  [* fun t => t⟦key⟧ ⟨1⟩ = 1 ∧ t⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ t⟦key⟧ ⟨2⟩ = 3 ∧ t⟦next⟧ ⟨2⟩ = Ref.null ∧
              t⟦target⟧ = 3 ∧ t⟦prev⟧ = ⟨2⟩ ∧ t⟦curr⟧ = Ref.null *] := by
  incorrectness_auto

-- =============================================================
-- Set operations (dedicated statements `setInsert` / `setRemove`)
-- =============================================================

/-- **Aliasing bug with set insert/remove.**  C++:

      admins.insert(u);     // promote the new admin
      admins.erase(v);      // demote the old admin   -- BUG: forgets u may equal v

    When `u` and `v` are the same node, the new admin ends up NOT in the set. -/
example :
  [* fun s => s⟦u⟧ = ⟨1⟩ ∧ s⟦v⟧ = ⟨1⟩ *]
  (Stmt.setInsert admins (fun s => s⟦u⟧);
   Stmt.setRemove admins (fun s => s⟦v⟧))
  [* fun t => t⟦u⟧ = ⟨1⟩ ∧ t⟦v⟧ = ⟨1⟩ ∧ t⟦admins⟧ ⟨1⟩ = false *] := by
  incorrectness_auto

/-- **Wrong set operator.**  C++:

      members = teamA ∩ teamB;   // BUG: should be teamA ∪ teamB

    With `teamA = {1}` and `teamB = ∅` the result is `∅` instead of `{1}`.
    Whole-set expressions (`SetV.union`, `SetV.inter`, …) are used inside
    `assign`, exactly like map reads. -/
example :
  [* fun s => s⟦teamA⟧ = SetV.insert (a := .ref) ⟨1⟩ SetV.empty ∧ s⟦teamB⟧ = SetV.empty *]
  (Stmt.assign members (fun s => SetV.inter (s⟦teamA⟧) (s⟦teamB⟧)))
  [* fun t => t⟦teamA⟧ = SetV.insert (a := .ref) ⟨1⟩ SetV.empty ∧ t⟦teamB⟧ = SetV.empty ∧
              t⟦members⟧ = SetV.empty *] := by
  incorrectness_auto

/-- **Set updates inside a loop: marks the wrong node.**  C++:

      while (curr != NULL) {
        visited.insert(next[curr]);   // BUG: should be visited.insert(curr)
        curr = next[curr];
      }

    On the list `⟨1⟩ → ⟨2⟩ → NULL` the head is never marked, while NULL is.
    Closed by unrolling the loop; no invariant is needed. -/
example :
  [* fun s => s⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ s⟦next⟧ ⟨2⟩ = Ref.null ∧ s⟦curr⟧ = ⟨1⟩ ∧
              s⟦visited⟧ ⟨0⟩ = false ∧ s⟦visited⟧ ⟨1⟩ = false ∧ s⟦visited⟧ ⟨2⟩ = false *]
  (Stmt.whileDo (fun s => s⟦curr⟧ ≠ Ref.null)
    (Stmt.setInsert visited (fun s => s⟦next⟧ (s⟦curr⟧));          -- BUG
     Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧))))
  [* fun t => t⟦next⟧ ⟨1⟩ = ⟨2⟩ ∧ t⟦next⟧ ⟨2⟩ = Ref.null ∧ t⟦curr⟧ = Ref.null ∧
              t⟦visited⟧ ⟨0⟩ = true ∧ t⟦visited⟧ ⟨1⟩ = false ∧ t⟦visited⟧ ⟨2⟩ = true *] := by
  incorrectness_auto

-- =============================================================
-- Sets: marking a node visited
-- =============================================================
/-- `visited : Var (.set .ref)` is a set of nodes; membership is `s⟦visited⟧ r = true`
    and insertion is a map write.  No new language construct is needed. -/
example :
  [* fun s => s⟦visited⟧ ⟨1⟩ = false ∧ s⟦curr⟧ = ⟨1⟩ *]
  (Stmt.mapUpdate visited (fun s => s⟦curr⟧) (fun _ => true))    -- visited[curr] := true
  [* fun t => t⟦visited⟧ ⟨1⟩ = true ∧ t⟦curr⟧ = ⟨1⟩ *] := by
  incorrectness_auto

-- =============================================================
-- Allocation alone
-- =============================================================
/-- `n := new` binds `n` to a fresh node and marks it allocated. -/
example :
  [* fun s => s⟦curr⟧ = ⟨1⟩ ∧ s.alloc ⟨3⟩ = false *]
  (Stmt.alloc n)
  [* fun t => t⟦curr⟧ = ⟨1⟩ ∧ t⟦n⟧ = ⟨3⟩ ∧ t.alloc ⟨3⟩ = true *] := by
  incorrectness_auto

-- =============================================================
-- Relation operations (dedicated statements `relInsert` / `relRemove`,
-- whole-relation expressions `RelV.*`)
-- =============================================================

/-- **Undirected edge removal, copy-paste bug.**  An undirected graph is kept
    as a symmetric relation `adj`; removing the edge `{u, v}` must delete both
    directions.  C++:

      adj.erase({u, v});
      adj.erase({u, v});     // BUG: copy-paste, should be adj.erase({v, u})

    The half-edge `(v, u)` survives: the graph is no longer symmetric. -/
example :
  [* fun s => s⟦u⟧ = ⟨1⟩ ∧ s⟦v⟧ = ⟨2⟩ ∧ s⟦adj⟧ ⟨1⟩ ⟨2⟩ = true ∧ s⟦adj⟧ ⟨2⟩ ⟨1⟩ = true *]
  (Stmt.relRemove adj (fun s => s⟦u⟧) (fun s => s⟦v⟧);
   Stmt.relRemove adj (fun s => s⟦u⟧) (fun s => s⟦v⟧))                 -- BUG: (v, u)
  [* fun t => t⟦u⟧ = ⟨1⟩ ∧ t⟦v⟧ = ⟨2⟩ ∧ t⟦adj⟧ ⟨1⟩ ⟨2⟩ = false ∧ t⟦adj⟧ ⟨2⟩ ⟨1⟩ = true *] := by
  incorrectness_auto

/-- **Loading a directed graph with reversed edges (loop).**  The edges come
    as two parallel arrays of nodes `src`, `dst`.  C++:

      for (i = 0; i < N; i++)
        E.insert({dst[i], src[i]});    // BUG: should be {src[i], dst[i]}

    On the path `⟨1⟩ → ⟨2⟩ → ⟨3⟩` the loaded relation is the reversed path:
    `(2, 1)` and `(3, 2)` are edges, `(1, 2)` and `(2, 3)` are not.  Closed
    by unrolling the loop; no invariant is needed. -/
example :
  [* fun s => s⟦src⟧ 0 = ⟨1⟩ ∧ s⟦dst⟧ 0 = ⟨2⟩ ∧ s⟦src⟧ 1 = ⟨2⟩ ∧ s⟦dst⟧ 1 = ⟨3⟩ ∧
      s⟦N⟧ = 2 ∧ s⟦i⟧ = 0 ∧
      s⟦E⟧ ⟨1⟩ ⟨2⟩ = false ∧ s⟦E⟧ ⟨2⟩ ⟨1⟩ = false ∧ s⟦E⟧ ⟨2⟩ ⟨3⟩ = false ∧ s⟦E⟧ ⟨3⟩ ⟨2⟩ = false *]
  (Stmt.whileDo (fun s => s⟦i⟧ < s⟦N⟧)
    (Stmt.relInsert E (fun s => s⟦dst⟧ (s⟦i⟧)) (fun s => s⟦src⟧ (s⟦i⟧));   -- BUG: reversed
     Stmt.assign i (fun s => s⟦i⟧ + 1)))
  [* fun t => t⟦src⟧ 0 = ⟨1⟩ ∧ t⟦dst⟧ 0 = ⟨2⟩ ∧ t⟦src⟧ 1 = ⟨2⟩ ∧ t⟦dst⟧ 1 = ⟨3⟩ ∧
      t⟦N⟧ = 2 ∧ t⟦i⟧ = 2 ∧
      t⟦E⟧ ⟨1⟩ ⟨2⟩ = false ∧ t⟦E⟧ ⟨2⟩ ⟨1⟩ = true ∧ t⟦E⟧ ⟨2⟩ ⟨3⟩ = false ∧ t⟦E⟧ ⟨3⟩ ⟨2⟩ = true *] := by
  incorrectness_auto

/-- **Composition in the wrong order.**  Role-based access control over
    numeric IDs: `userRole` relates users to roles, `rolePerm` roles to
    permissions, and the permissions of a user are `userRole ⨾ rolePerm`.

      userPerm = compose(rolePerm, userRole);   // BUG: compose(userRole, rolePerm)

    User 1 has role 2, which grants permission 3.  The buggy composition is
    empty, so user 1 ends up with no permission at all (the correct result
    would be `{(1, 3)}`).  Since IDs are plain `nat`s, the swapped arguments
    type-check. -/
example :
  [* fun s => s⟦userRole⟧ = RelV.insert (a := .nat) (b := .nat) 1 2 RelV.empty ∧
              s⟦rolePerm⟧ = RelV.insert (a := .nat) (b := .nat) 2 3 RelV.empty *]
  (Stmt.assign userPerm (fun s => RelV.comp (s⟦rolePerm⟧) (s⟦userRole⟧)))   -- BUG: order
  [* fun t => t⟦userRole⟧ = RelV.insert (a := .nat) (b := .nat) 1 2 RelV.empty ∧
              t⟦rolePerm⟧ = RelV.insert (a := .nat) (b := .nat) 2 3 RelV.empty ∧
              t⟦userPerm⟧ = RelV.empty *] := by
  incorrectness_auto

/-- **Mutual follows with `∪` instead of `∩` (uses the converse).**

      mutualFollow = follows ∪ follows⁻¹;   // BUG: should be follows ∩ follows⁻¹

    User 1 follows user 2 but not the other way round.  The correct result
    is empty; the buggy one claims that 1 and 2 follow each other. -/
example :
  [* fun s => s⟦follows⟧ = RelV.insert (a := .nat) (b := .nat) 1 2 RelV.empty *]
  (Stmt.assign mutualFollow (fun s => RelV.union (s⟦follows⟧) (RelV.inv (s⟦follows⟧))))
  [* fun t => t⟦follows⟧ = RelV.insert (a := .nat) (b := .nat) 1 2 RelV.empty ∧
              t⟦mutualFollow⟧ = RelV.insert (a := .nat) (b := .nat) 1 2
                                  (RelV.insert 2 1 RelV.empty) *] := by
  incorrectness_auto

end MapLang.Examples
