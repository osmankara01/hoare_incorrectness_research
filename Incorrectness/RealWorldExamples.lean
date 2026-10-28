import Incorrectness.VCGen
import Incorrectness.Seq

open Language
open Incorrectness

/-!
# Data-structure abstractions (advisor-requested form)

The state model in this project is fixed: `State = String → Nat`. To
faithfully encode the data structures the advisor asked for —
**"array as a map/function `Nat → Nat`"** and **"linked list with a
`Node` type, `next : Node → Node` and `key : Node → Nat` maps"** — we
do *not* extend the language. Instead we expose those maps as proper
Lean-level functions of the state. Each function reads a deterministic
naming scheme of state slots, so updating "the map at index `i`" is
realised by case-splitting on the runtime value of `i` and updating the
corresponding slot.

  arr     : State → Nat  → Nat     -- the array map (4-slot pool)
  keyOf   : State → Node → Nat     -- the key  map (3-node pool)
  nextOf  : State → Node → Node    -- the next map (3-node pool, 0 = NULL)

These definitions are `@[simp]` so once the iteration-counter case-split
fixes the index, the if-cascade reduces and proofs go through with the
existing `il_close` simp set.
-/

/-!
The encoding mirrors a C `struct Node { unsigned int key; Node* next; };`:

  • `Node` is a node identifier (a `Nat`). The value `0` is NULL.
  • `key  : Node → Nat`   ─ each node has a key field
  • `next : Node → Node`  ─ each node has a next-pointer field

In a purely functional setting the maps `key` and `next` must close over the
*current* heap, because the program mutates them (`key_3 := target`,
`next_2 := 3`). We expose that by giving each map a `State` parameter:
`keyOf s` is the `Node → Nat` map *at state s*. Fix `s` and you get the
abstract `Node → Nat` field.

Slots are addressed by `s!"key_{n}"` / `s!"next_{n}"`, so there is no
hard-coded bound on the node count — the encoding works for any
`Node = Nat`. -/

abbrev Node : Type := Nat

/-- Array of unbounded capacity viewed as a map `i ↦ s "a{i}"`. -/
def arr    (s : State) (i : Nat)  : Nat  := s s!"a{i}"

/-- Key field of node `n`, read from the current state. -/
def keyOf  (s : State) (n : Node) : Nat  := s s!"key_{n}"

/-- Next field of node `n`, read from the current state. -/
def nextOf (s : State) (n : Node) : Node := s s!"next_{n}"

-- Sanity check: the unbounded definitions reduce to slot reads by `rfl`.
example (s : State) : keyOf  s 4   = s "key_4"  := rfl
example (s : State) : nextOf s 42  = s "next_42" := rfl
example (s : State) : arr    s 17  = s "a17"    := rfl

/-!
## Bridging definitions and `simp`

The definitions above already reduce by `rfl`: for *any* `n : Nat` literal,
`keyOf s n` is definitionally `s "key_<n>"`. The two `example`s just above
demonstrate this for `n = 4, 42, 17` — no per-literal lemma needed.

However, `simp` by itself does not normalise `Nat.repr n` for concrete `n`
inside string interpolation. We bridge this with one **simproc** —
fifteen lines of meta-code that match `keyOf s n` / `nextOf s n` / `arr s i`
for *any* Nat literal `n` and rewrite to the corresponding slot read by
`rfl`. The result: minimal proof boilerplate, maximum automation. -/

open Lean Meta Simp in
/-- Simp-procedure: rewrite `keyOf s ⟨lit⟩`, `nextOf s ⟨lit⟩`, `arr s ⟨lit⟩`
    to the corresponding state slot read, for any Nat literal. -/
simproc ↓ reduceFieldRead (keyOf _ _) := fun e => do
  let_expr keyOf s n := e | return .continue
  let some nVal := n.nat? | return .continue
  let slot := mkStrLit s!"key_{nVal}"
  let result := mkApp s slot
  return .visit { expr := result, proof? := ← mkEqRefl result }

open Lean Meta Simp in
simproc ↓ reduceNextRead (nextOf _ _) := fun e => do
  let_expr nextOf s n := e | return .continue
  let some nVal := n.nat? | return .continue
  let slot := mkStrLit s!"next_{nVal}"
  let result := mkApp s slot
  return .visit { expr := result, proof? := ← mkEqRefl result }

open Lean Meta Simp in
simproc ↓ reduceArrRead (arr _ _) := fun e => do
  let_expr arr s i := e | return .continue
  let some iVal := i.nat? | return .continue
  let slot := mkStrLit s!"a{iVal}"
  let result := mkApp s slot
  return .visit { expr := result, proof? := ← mkEqRefl result }

/-!
# Real-World Bug Detection Examples

This file collects examples that mimic *realistic* bug patterns
found in production code, encoded within our Nat-only state model.
Each example demonstrates that an IL triple of the form
`[precondition] buggy_program [bug_state]` is **provable**, meaning
the bug state is genuinely reachable from the precondition.

In standard usage the user writes a postcondition describing the
*intended* outcome and `incorrectness_auto` proves whether a state
violating that intent is reachable. When the proof succeeds, a bug
exists; when it fails, the bug pattern doesn't manifest in our model.

Examples 1–10 are each closed by a single call to the unified
`incorrectness_auto` dispatcher (loop-free path first, then bounded
while search). The data-structure examples 11–13 use the invariant
tactics instead — `incorrectness_auto_inv_split N inv` for a concrete
iteration bound (11, 12) and the fully parametric `incorrectness_auto_inv`
for a symbolic bound (13) — composed with `seq_intro` where the program
has a find-then-mutate phase split.

The bug categories covered here:

| #  | Category                                    | Loop? | Tactic |
|----|---------------------------------------------|-------|--------|
| 1  | `<` vs `≤` in withdrawal check              | no    | `incorrectness_auto` |
| 2  | `≥` vs `>` in discount threshold            | no    | `incorrectness_auto` |
| 3  | `>` vs `≥` in age verification              | no    | `incorrectness_auto` |
| 4  | Logical AND vs OR in access control         | no    | `incorrectness_auto` |
| 5  | Off-by-one: loop-counter starts at 0        | yes   | `incorrectness_auto` |
| 6  | `≤` vs `<` in loop guard                    | yes   | `incorrectness_auto` |
| 7  | Loop runs one extra time                    | yes   | `incorrectness_auto` |
| 8  | Two-stage validation, second stage skipped  | no    | `incorrectness_auto` |
| 9  | Sequence of assertions that miss a case     | no    | `incorrectness_auto` |
| 10 | Nested loops where outer escapes too early  | yes   | `incorrectness_auto` |
| 11 | Sorted-array insert, `<` vs `≤` (concrete)  | yes   | `incorrectness_auto_inv_split` |
| 12 | Pointer linked-list insert, `<` vs `≤`      | yes   | `incorrectness_auto_inv_split` |
| 13 | Linked-list scan, `<` vs `≤`, symbolic `N`  | yes   | `incorrectness_auto_inv` |
| 14 | Sorted-array position search, `>` vs `≥`    | yes   | `incorrectness_auto_inv_split` |
| 15 | Linked-list position scan, `≤` vs `<`       | yes   | `incorrectness_auto_inv_split` |
-/

-- =============================================================
-- Example 1 — Bank withdrawal validator: `<` instead of `≤`
-- =============================================================
/-
A banking system *should* allow withdrawal whenever the requested
amount is ≤ balance. The buggy code uses strict `<`, so a request
equal to the balance is incorrectly rejected.

Scenario: balance = 100, withdrawal = 100. The user expects approval,
but the buggy program lands in the rejection branch. This bug state
is reachable, hence provable.
-/
example :
  [* (fun s => s "balance" = 100 ∧ s "withdrawal" = 100) *]
  (Stmt.ifThenElse
    (fun s => s "withdrawal" < s "balance")    -- BUG: should be ≤
    (Stmt.assign "approved" (fun _ => 1))
    (Stmt.assign "approved" (fun _ => 0)))
  [* (fun t => t "approved" = 0 ∧ t "balance" = 100 ∧ t "withdrawal" = 100) *] := by
  incorrectness_auto

-- =============================================================
-- Example 2 — Discount threshold: `≥` instead of `>`
-- =============================================================
/-
The pricing rule says "10% discount for orders over $1000".
A buggy implementation uses `≥`, applying the discount at exactly
$1000 when it shouldn't.

Scenario: amount = 1000. Buggy program applies the discount.
Bug state reachable.
-/
example :
  [* (fun s => s "amount" = 1000) *]
  (Stmt.ifThenElse
    (fun s => s "amount" ≥ 1000)               -- BUG: should be >
    (Stmt.assign "discounted" (fun _ => 1))
    (Stmt.assign "discounted" (fun _ => 0)))
  [* (fun t => t "discounted" = 1 ∧ t "amount" = 1000) *] := by
  incorrectness_auto

-- =============================================================
-- Example 3 — Age verification: `>` instead of `≥`
-- =============================================================
/-
Age gate should permit `age ≥ 18`. Buggy implementation uses strict
`>`, rejecting exactly-18-year-olds.

Scenario: age = 18. Buggy program denies access. Bug reachable.
-/
example :
  [* (fun s => s "age" = 18) *]
  (Stmt.ifThenElse
    (fun s => s "age" > 18)                    -- BUG: should be ≥
    (Stmt.assign "allowed" (fun _ => 1))
    (Stmt.assign "allowed" (fun _ => 0)))
  [* (fun t => t "allowed" = 0 ∧ t "age" = 18) *] := by
  incorrectness_auto

-- =============================================================
-- Example 4 — Access control: AND vs OR confusion
-- =============================================================
/-
A system should grant access only to users who are BOTH admin AND
active. The buggy version uses OR, so any active non-admin user
also gets access.

Scenario: admin = 0, active = 1. Buggy program grants access.
Privilege-escalation bug; reachable.
-/
example :
  [* (fun s => s "admin" = 0 ∧ s "active" = 1) *]
  (Stmt.ifThenElse
    (fun s => s "admin" = 1 ∨ s "active" = 1)  -- BUG: should be ∧
    (Stmt.assign "access" (fun _ => 1))
    (Stmt.assign "access" (fun _ => 0)))
  [* (fun t => t "access" = 1 ∧ t "admin" = 0 ∧ t "active" = 1) *] := by
  incorrectness_auto

-- =============================================================
-- Example 5 — Loop guard: `≤` instead of `<`
-- =============================================================
/-
A loop intended to run exactly 3 times (for x = 0, 1, 2) but the
buggy guard uses `≤ 3` instead of `< 3`, so it runs 4 times.

Final state: x = 4, when the programmer expected x = 3.
Bug reachable via 4 iterations.
-/
example :
  [* (fun s => s "x" = 0) *]
  (Stmt.whileDo
    (fun s => s "x" ≤ 3)                       -- BUG: should be < 3
    (Stmt.assign "x" (fun s => s "x" + 1)))
  [* (fun t => t "x" = 4) *] := by
  incorrectness_auto

-- =============================================================
-- Example 6 — Loop runs one extra iteration (`<` boundary)
-- =============================================================
/-
A loop processes counter from initial value 0 up to (but not
including) some threshold. The intended threshold is 5, but a
buggy off-by-one uses 6, running one extra time.
-/
example :
  [* (fun s => s "counter" = 0) *]
  (Stmt.whileDo
    (fun s => s "counter" < 6)                 -- BUG: intended 5
    (Stmt.assign "counter" (fun s => s "counter" + 1)))
  [* (fun t => t "counter" = 6) *] := by
  incorrectness_auto

-- =============================================================
-- Example 7 — Conditional bug + assignment in sequence
-- =============================================================
/-
A request validator: comparison bug grants access at boundary.
The bug: comparison uses `≥` instead of strict `>`. With input=50
and the threshold also 50, the buggy code proceeds to "approved"
state when it should not.
-/
example :
  [* (fun s => s "input" = 50) *]
  (Stmt.ifThenElse
    (fun s => s "input" ≥ 50)                  -- BUG: intended > 50
    (Stmt.assign "result" (fun _ => 1))        -- approved
    (Stmt.assign "result" (fun _ => 0)))       -- rejected
  [* (fun t => t "result" = 1 ∧ t "input" = 50) *] := by
  incorrectness_auto

-- =============================================================
-- Example 8 — Counter that wraps past intended limit
-- =============================================================
/-
A "rate limiter" intended to permit at most 3 requests but the
buggy guard uses a different threshold, allowing the counter to
exceed the intended cap.
-/
example :
  [* (fun s => s "requests" = 0) *]
  (Stmt.whileDo
    (fun s => s "requests" < 5)                -- BUG: intended 3
    (Stmt.assign "requests" (fun s => s "requests" + 1)))
  [* (fun t => t "requests" = 5) *] := by
  incorrectness_auto

-- =============================================================
-- Example 9 — Sequence of assertions that miss a case
-- =============================================================
/-
A pipeline that asserts intermediate properties. The first assert
catches malformed input. But the assert is too lax: it only checks
`x ≠ 0`, missing the case `x = 1` which the rest of the program
treats specially. After the assert succeeds for x = 1, the program
proceeds to a wrong branch.
-/
example :
  [* (fun s => s "x" = 1) *]
  (Stmt.seq
    (Stmt.assert (fun s => s "x" ≠ 0))         -- assert too weak
    (Stmt.ifThenElse
      (fun s => s "x" > 1)
      (Stmt.assign "result" (fun _ => 100))
      (Stmt.assign "result" (fun _ => 999))))  -- "error sentinel"
  [* (fun t => t "result" = 999 ∧ t "x" = 1) *] := by
  incorrectness_auto

-- =============================================================
-- Example 10 — Nested loops where outer escapes too early
-- =============================================================
/-
An outer loop that's supposed to cover all values but the inner
loop's side effect on the outer counter causes early exit.

Here we encode a single while loop where the body advances `x` by
1, but a second variable `y` should remain 0 — yet the buggy body
also touches `y`. After 2 iterations: x=2, y=2 (not the intended
y=0). The bug: y mutated unintentionally.
-/
example :
  [* (fun s => s "x" = 0 ∧ s "y" = 0) *]
  (Stmt.whileDo
    (fun s => s "x" < 2)
    (Stmt.seq
      (Stmt.assign "x" (fun s => s "x" + 1))
      (Stmt.assign "y" (fun s => s "y" + 1))))   -- BUG: y not supposed to change
  [* (fun t => t "x" = 2 ∧ t "y" = 2) *] := by
  incorrectness_auto

-- =============================================================
-- Example 11 — Sorted array insert with shift: `<` vs `≤` bug
-- =============================================================
/-
**The classic sorted-array insert duplication bug** — full pipeline:
find-position loop *and* element-shifting, producing a verified
duplicate in the final array.

## The array as a map

Conceptually the array is a map `Nat → Nat`. We encode a 4-slot
fixed-capacity array via state variables `a0, a1, a2, a3`, plus a
length `len`. The runtime "function view" `a[i]` is the Lean
expression `if i = 0 then s "a0" else if i = 1 then s "a1" else …`.

## The algorithm (sorted-insert avoiding duplicates)

  -- Phase 1: scan to find the right insert index (loop)
  i := 0
  while i < len ∧ a[i] ≤ target:     -- BUG: should use strict `<`
    i := i + 1
  pos := i

  -- Phase 2: shift elements [pos .. len-1] one slot right
  a3 := if pos ≤ 2 then a2 else a3
  a2 := if pos ≤ 1 then a1 else a2
  a1 := if pos ≤ 0 then a0 else a1
  -- write target at the freed slot
  (assign target to the appropriate slot)
  len := len + 1

The bug: the `≤` walks past an equal element. Combined with the
shift+insert phase, this places the new value *after* the existing
equal element rather than skipping insertion.

## Concrete trace, target = 3, initial [1, 3, 5]

  Phase 1 (buggy):
    i=0  a0=1 ≤ 3 ✓ → i=1
    i=1  a1=3 ≤ 3 ✓ (BUG, equals!) → i=2
    i=2  a2=5 ≤ 3 ✗ → exit
    pos := 2

  Phase 2 (shift+insert at pos=2):
    a3 := a2 = 5       (shift)
    a2 unchanged (pos ≤ 1 is false)
    a1 unchanged (pos ≤ 0 is false)
    a2 := 3            (write target at pos=2)
    len := 4

  Final array: [1, 3, 3, 5]   ← duplicate!  Bug demonstrated.

## What we prove

The IL triple is `[initial] full_program [duplicate_state]`. We split
the program at the seq boundary using `seq_intro`:
- Phase 1 is closed by `incorrectness_auto_inv_split` with an indexed
  invariant tracking `i` and `pos`.
- Phase 2 (loop-free) is closed by `incorrectness_auto`.

The intermediate assertion captures the state after Phase 1:
`pos = 2`, all array values unchanged, etc.
-/

example :
  -- Precondition: the array map `arr s` has the initial sequence [1, 3, 5, 0]
  -- (and length 3, target 3). `arr s 0 = s "a0"` etc. via the targeted simp
  -- lemmas, so this form is definitionally equivalent to the slot view.
  [* (fun s => arr s 0 = 1 ∧ arr s 1 = 3 ∧ arr s 2 = 5 ∧ arr s 3 = 0 ∧
               s "len" = 3 ∧ s "target" = 3 ∧
               s "i" = 0 ∧ s "pos" = 3) *]
  (Stmt.seq
    -- Phase 1: find pos (buggy: ≤ should be <)
    (Stmt.whileDo
      (fun s => s "i" < 3 ∧ s "pos" = 3)
      (Stmt.seq
        (Stmt.ifThenElse
          (fun s =>
            (s "i" = 0 ∧ s "a0" > s "target") ∨
            (s "i" = 1 ∧ s "a1" > s "target") ∨
            (s "i" = 2 ∧ s "a2" > s "target"))   -- BUG: > should be ≥
          (Stmt.assign "pos" (fun s => s "i"))
          Stmt.skip)
        (Stmt.assign "i" (fun s => s "i" + 1))))
    -- Phase 2: shift right + insert at pos (all conditionals on pos)
    (Stmt.seq
      (Stmt.assign "a3" (fun s => if s "pos" ≤ 2 then s "a2" else s "a3"))
      (Stmt.seq
        (Stmt.assign "a2" (fun s => if s "pos" ≤ 1 then s "a1" else s "a2"))
        (Stmt.seq
          (Stmt.assign "a1" (fun s => if s "pos" ≤ 0 then s "a0" else s "a1"))
          (Stmt.seq
            (Stmt.assign "a0" (fun s => if s "pos" = 0 then s "target" else s "a0"))
            (Stmt.seq
              (Stmt.assign "a1" (fun s => if s "pos" = 1 then s "target" else s "a1"))
              (Stmt.seq
                (Stmt.assign "a2" (fun s => if s "pos" = 2 then s "target" else s "a2"))
                (Stmt.seq
                  (Stmt.assign "a3" (fun s => if s "pos" = 3 then s "target" else s "a3"))
                  (Stmt.assign "len" (fun s => s "len" + 1))))))))))
  -- Postcondition: duplicate state [1, 3, 3, 5], len=4
  -- (i = 3 included because Phase 2 doesn't change it, so the bug-state must
  --  preserve the loop-exit value from Phase 1.)
  -- Postcondition: the map `arr t` now reads [1, 3, 3, 5] — the duplicate
  -- bug state with two 3's in adjacent slots, length 4.
  [* (fun t => arr t 0 = 1 ∧ arr t 1 = 3 ∧ arr t 2 = 3 ∧ arr t 3 = 5 ∧
               t "len" = 4 ∧ t "target" = 3 ∧ t "i" = 3 ∧ t "pos" = 2) *] := by
  -- Split at the seq boundary. Intermediate state: end of Phase 1.
  apply seq_intro (Q := fun s =>
    arr s 0 = 1 ∧ arr s 1 = 3 ∧ arr s 2 = 5 ∧ arr s 3 = 0 ∧
    s "len" = 3 ∧ s "target" = 3 ∧
    s "i" = 3 ∧ s "pos" = 2)
  -- ▶ Phase 1: while loop with case-split on iteration counter `i` up to 3.
  · incorrectness_auto_inv_split 3 (fun i s =>
      arr s 0 = 1 ∧ arr s 1 = 3 ∧ arr s 2 = 5 ∧ arr s 3 = 0 ∧
      s "len" = 3 ∧ s "target" = 3 ∧
      s "i" = i ∧ i ≤ 3 ∧
      (i ≤ 2 → s "pos" = 3) ∧
      (i = 3 → s "pos" = 2))
  -- ▶ Phase 2: loop-free shift+insert. Try `incorrectness_auto` first.
  · incorrectness_auto

-- =============================================================
-- Example 12 — Pointer-based sorted-list insert: `<` vs `≤` bug
-- =============================================================
/-
**The pointer-based variant of Example 11** — same `<` vs `≤` mistake,
but now on a real singly-linked list (no arrays). Advisor-requested
form: `Node` type with `keyOf : Node → Nat` and `nextOf : Node → Node`
maps, defined above as honest Lean functions over the state.

## The example in plain English

A sorted singly-linked list. Each node has a *key* (natural number)
and a *next* pointer (another node or NULL). Inserting a new value
into a sorted list **without duplicating an existing key** is done by
scanning from the head until the first node whose key is **strictly
greater** than the target, then splicing the new node in just before
that node.

## Where the bug lives

The buggy scan uses `≤` instead of `<`. When the target value already
appears in the list, the scan walks *past* the equal node and the
splice phase inserts a duplicate after the original.

## Mathematical statement

  Pre:  a finite sorted list  L = (k₁, k₂, …, kₙ)  with kᵢ < kᵢ₊₁,
        head pointing at k₁, and a target value `t` such that
        ∃ j. k_j = t   (i.e. `t` is already in the list).

  Buggy program:  insert(t) using the loop guard `key[curr] ≤ t`.

  Post:  reachable state where L′ = (k₁, …, k_j, t, k_{j+1}, …, kₙ)
         contains two adjacent copies of `t`.  → the duplicate is a bug.

Below we instantiate this at n = 2 with  L = (1, 3),  t = 3.

## Concrete initial configuration

  head    = 1
  keyOf 1 = 1,  nextOf 1 = 2
  keyOf 2 = 3,  nextOf 2 = 0     -- NULL terminator
  keyOf 3 = 0,  nextOf 3 = 0     -- pre-allocated free slot for new node
  target  = 3,  prev = 0 (NULL sentinel),  curr = 1

## The buggy algorithm (informal)

    while curr ≠ 0 ∧ keyOf curr ≤ target:    // BUG: should be strict `<`
      prev := curr
      curr := nextOf curr
    keyOf 3  := target                       -- initialise new node 3
    nextOf 3 := curr
    if prev = 0 then head := 3
    else nextOf prev := 3                    -- splice in

## Concrete bug trace (target = 3)

  Phase 1 — find position:
    iter 0:  curr=1, keyOf 1 = 1, 1 ≤ 3 ✓  → prev=1, curr=nextOf 1 = 2
    iter 1:  curr=2, keyOf 2 = 3, 3 ≤ 3 ✓ (BUG, equal!) → prev=2, curr=nextOf 2 = 0
    iter 2:  curr=0, guard fails (curr = 0), exit

  Phase 2 — splice (prev = 2, curr = 0):
    keyOf  3 := 3
    nextOf 3 := 0
    prev = 2 ≠ 0,  so  nextOf prev = nextOf 2 := 3

  Final list:  1 → 2 → 3 → NULL  with keys [1, 3, 3].   ← DUPLICATE.

## How the proof closes it

We split the program at the seq boundary with `seq_intro`, then:

  · Phase 1 (the loop)         — closed by  `incorrectness_auto_inv_split 2 inv`
                                  with an indexed invariant pinning
                                  (prev, curr) per iteration.

  · Phase 2 (loop-free splice) — closed by  `incorrectness_auto`.

Both phases are discharged by the *general* automation: Phase 1 by the same
invariant tactic that closes the array loop of Example 11 (only the invariant
differs), and Phase 2 by the unified loop-free dispatcher. The pointer body's
two simultaneous existentials (over the pre-values of `prev` and `curr`) are
back-solved by `il_close`'s AC-normalising fallback (`il_close_hard`), which
floats each invariant-pinned equation next to its binding `∃`.
-/

example :
  [* (fun s =>
        s "head" = 1 ∧
        s "key_1"  = 1 ∧ s "next_1" = 2 ∧
        s "key_2"  = 3 ∧ s "next_2" = 0 ∧
        s "key_3"  = 0 ∧ s "next_3" = 0 ∧
        s "target" = 3 ∧
        s "prev"   = 0 ∧ s "curr"   = 1) *]
  (Stmt.seq
    -- Phase 1: scan via the buggy `≤`
    (Stmt.whileDo
      (fun s => s "curr" ≠ 0 ∧ keyOf s (s "curr") ≤ s "target")  -- BUG: ≤ not <
      (Stmt.seq
        (Stmt.assign "prev" (fun s => s "curr"))
        (Stmt.assign "curr" (fun s => nextOf s (s "curr")))))
    -- Phase 2: splice in new node (id = 3)
    (Stmt.seq
      (Stmt.assign "key_3"  (fun s => s "target"))
      (Stmt.seq
        (Stmt.assign "next_3" (fun s => s "curr"))
        (Stmt.ifThenElse
          (fun s => s "prev" = 0)
          (Stmt.assign "head" (fun _ => 3))                       -- list was empty
          -- nextOf prev := 3, expanded as three guarded slot writes
          (Stmt.seq
            (Stmt.assign "next_1" (fun s => if s "prev" = 1 then 3 else s "next_1"))
            (Stmt.seq
              (Stmt.assign "next_2" (fun s => if s "prev" = 2 then 3 else s "next_2"))
              (Stmt.assign "next_3" (fun s => if s "prev" = 3 then 3 else s "next_3"))))))))
  -- Post: the duplicate-key bug state
  [* (fun t =>
        t "head"   = 1 ∧
        t "key_1"  = 1 ∧ t "next_1" = 2 ∧
        t "key_2"  = 3 ∧ t "next_2" = 3 ∧   -- changed: 0 → 3 (links to new)
        t "key_3"  = 3 ∧ t "next_3" = 0 ∧   -- new node has the duplicate key
        t "target" = 3 ∧
        t "prev"   = 2 ∧ t "curr"   = 0) *] := by
  -- Intermediate state: end of Phase 1.
  apply seq_intro (Q := fun s =>
    s "head"   = 1 ∧
    s "key_1"  = 1 ∧ s "next_1" = 2 ∧
    s "key_2"  = 3 ∧ s "next_2" = 0 ∧
    s "key_3"  = 0 ∧ s "next_3" = 0 ∧
    s "target" = 3 ∧
    s "prev"   = 2 ∧ s "curr"   = 0)
  -- ▶ Phase 1 — closed in ONE LINE by the general invariant tactic.
  --   The body has two sequential pointer-dereferences
  --   (`prev := curr; curr := nextOf curr`) producing TWO simultaneous
  --   existentials over (old_prev, old_curr), both pinned by the invariant.
  --   `il_close`'s AC-fallback (`il_close_hard`) back-solves those buried
  --   witnesses, so the *same* tactic that closes the array loop (Example 11)
  --   closes this pointer loop too — only the invariant differs.
  · incorrectness_auto_inv_split 2 (fun i s =>
      s "head"   = 1 ∧
      s "key_1"  = 1 ∧ s "next_1" = 2 ∧
      s "key_2"  = 3 ∧ s "next_2" = 0 ∧
      s "key_3"  = 0 ∧ s "next_3" = 0 ∧
      s "target" = 3 ∧
      i ≤ 2 ∧ s "prev" = i ∧
      s "curr" = (if i ≤ 1 then i + 1 else 0))
  -- ▶ Phase 2 — loop-free splice; closed by `incorrectness_auto`.
  · incorrectness_auto

-- =============================================================
-- Example 13 — SYMBOLIC-length list scan: `<` vs `≤` bug, parametric in N
-- =============================================================
/-
**The point of this example.** Examples 11 and 12 fix a *concrete* number of
list/array cells, so the loop runs a statically known number of times and we
close it with `incorrectness_auto_inv_split N` (which enumerates the iteration
counter `0,1,…,N`). Here the list length is a **symbolic parameter `N`** — the
loop runs an unknown-at-compile-time number of times — and we still close the
triple with **no concrete integer bound**, using the parametric
`incorrectness_auto_inv`. This is the direct answer to "can you handle a
general N, not just a fixed example?".

## The example in plain English

A sorted singly-linked list of `N` nodes at positions `0, 1, …, N-1` (node `j`
has key `j`; `next` of node `j` is `j+1`; position `N` is the past-the-end /
NULL boundary). We scan from the head with a `prev`/`curr` pointer pair to walk
to the end of the list.

## Where the bug lives

The scan uses `curr ≤ N` where it should use `curr < N`. With `<`, the walk
stops with `curr = N` (one past the last valid index `N-1`, i.e. exactly at the
NULL boundary — correct). With the buggy `≤`, it takes **one extra step**:
`curr` overshoots to `N+1` and `prev` lands on `N` (the NULL boundary itself).
A subsequent splice through `prev = N` writes *past the end of the list* — a
classic off-by-one / out-of-bounds bug, the pointer analogue of Example 12's
duplicate.

## Mathematical statement (parametric in N)

  Pre:   curr = 0,  prev = 0        (N is an arbitrary symbolic Nat)
  Loop:  while curr ≤ N do  prev := curr;  curr := curr + 1
  Post:  curr = N + 1  ∧  prev = N   (the reachable over-run bug state)

## Why one line closes it

The indexed invariant `Inv i s := curr = i ∧ prev = i-1 ∧ i ≤ N+1` is
inductive: the body's two simultaneous existentials (old `curr`, old `prev`)
are pinned by `Inv i` to the *symbolic* values `i` and `i-1`. `il_close`'s
AC-normalising fallback (`il_close_hard`) floats those pinned equations next
to their binding `∃` and eliminates the witnesses — **uniformly in `i`**, with
no case-split on the iteration count. Hence a genuinely parametric proof.
-/
example :
  [* (fun s => s "curr" = 0 ∧ s "prev" = 0) *]
  (Stmt.whileDo
    (fun s => s "curr" ≤ s "N")                      -- BUG: ≤ should be <
    (Stmt.seq
      (Stmt.assign "prev" (fun s => s "curr"))
      (Stmt.assign "curr" (fun s => s "curr" + 1))))
  [* (fun t => t "curr" = t "N" + 1 ∧ t "prev" = t "N") *] := by
  -- SYMBOLIC N: no concrete iteration bound — the parametric invariant tactic
  -- closes it uniformly in the iteration counter.
  incorrectness_auto_inv (fun i s => s "curr" = i ∧ s "prev" = i - 1 ∧ i ≤ s "N" + 1)

-- =============================================================
-- Example 14 — Sorted-array position search: `>` vs `≥` off-by-one
-- =============================================================
/-
A sorted array `[1, 3, 5]` and a target `3` that already appears. To find
where `target` belongs, the code scans left-to-right for the first cell whose
value is *greater than or equal to* the target; that index is the correct
insertion position (here `1`, immediately in front of the existing `3`).

## Where the bug lives

The scan tests `a[i] > target` where it should test `a[i] ≥ target`. Since the
existing `3` is not strictly greater than the target, the scan walks past it
and only stops at `5`, so the computed position `pos` overshoots to `2` instead
of `1` — the position that inserts a duplicate after the original.

## Mathematical statement

  Pre:   a = [1, 3, 5],  target = 3,  i = 0,  pos = 3 (unset sentinel)
  Loop:  while i < 3 ∧ pos = 3 do
           if a[i] > target then pos := i;  i := i + 1
  Post:  pos = 2   (the overshot, wrong insertion position)

The loop runs a fixed ≤ 3 iterations, so the case-splitting invariant tactic
enumerates the counter and closes each case.
-/
example :
  [* (fun s => s "a0" = 1 ∧ s "a1" = 3 ∧ s "a2" = 5 ∧
               s "target" = 3 ∧ s "i" = 0 ∧ s "pos" = 3) *]
  (Stmt.whileDo
    (fun s => s "i" < 3 ∧ s "pos" = 3)
    (Stmt.seq
      (Stmt.ifThenElse
        (fun s =>
          (s "i" = 0 ∧ s "a0" > s "target") ∨
          (s "i" = 1 ∧ s "a1" > s "target") ∨
          (s "i" = 2 ∧ s "a2" > s "target"))          -- BUG: > should be ≥
        (Stmt.assign "pos" (fun s => s "i"))
        Stmt.skip)
      (Stmt.assign "i" (fun s => s "i" + 1))))
  [* (fun t => t "a0" = 1 ∧ t "a1" = 3 ∧ t "a2" = 5 ∧ t "target" = 3 ∧
               t "i" = 3 ∧ t "pos" = 2) *] := by
  incorrectness_auto_inv_split 3 (fun i s =>
    s "a0" = 1 ∧ s "a1" = 3 ∧ s "a2" = 5 ∧ s "target" = 3 ∧
    s "i" = i ∧ i ≤ 3 ∧ (i ≤ 2 → s "pos" = 3) ∧ (i = 3 → s "pos" = 2))

-- =============================================================
-- Example 15 — Linked-list position scan: `≤` vs `<` off-by-one
-- =============================================================
/-
A sorted singly-linked list with two nodes, keys `1 → 3` (node `1` then node
`2`, with `next_2 = 0` as the NULL terminator), and a target `3` that already
appears. A `prev`/`curr` pointer pair walks the list to find where `target`
belongs: it should stop at the first node whose key is *not less than* the
target.

## Where the bug lives

The scan guard is `key[curr] ≤ target` where it should be `key[curr] < target`.
Since node `2`'s key equals the target, the buggy `≤` advances one node too
far: `curr` runs off the end (to NULL, `0`) while `prev` lands on node `2` —
the node holding the equal key. A splice through `prev` would insert a second
`3`.

## Mathematical statement

  Pre:   keys 1 → 3 (nodes 1, 2),  target = 3,  prev = 0,  curr = 1
  Loop:  while curr ≠ 0 ∧ key[curr] ≤ target do  prev := curr;  curr := next[curr]
  Post:  prev = 2 ∧ curr = 0   (the scan overran the equal node)
-/
example :
  [* (fun s => s "key_1" = 1 ∧ s "next_1" = 2 ∧ s "key_2" = 3 ∧ s "next_2" = 0 ∧
               s "target" = 3 ∧ s "prev" = 0 ∧ s "curr" = 1) *]
  (Stmt.whileDo
    (fun s => s "curr" ≠ 0 ∧ keyOf s (s "curr") ≤ s "target")   -- BUG: ≤ should be <
    (Stmt.seq
      (Stmt.assign "prev" (fun s => s "curr"))
      (Stmt.assign "curr" (fun s => nextOf s (s "curr")))))
  [* (fun t => t "key_1" = 1 ∧ t "next_1" = 2 ∧ t "key_2" = 3 ∧ t "next_2" = 0 ∧
               t "target" = 3 ∧ t "prev" = 2 ∧ t "curr" = 0) *] := by
  incorrectness_auto_inv_split 2 (fun i s =>
    s "key_1" = 1 ∧ s "next_1" = 2 ∧ s "key_2" = 3 ∧ s "next_2" = 0 ∧
    s "target" = 3 ∧ i ≤ 2 ∧ s "prev" = i ∧ s "curr" = (if i ≤ 1 then i + 1 else 0))
