import MapLang.VCGen

/-!
# Linked lists in MapLang — the advisor's arbitrary-list insert example

This file states and proves the example from the last meeting:

    [ ∃ node n reachable from head with key n = y ]
        insert y into the list starting from head        (buggy `≤` scan)
    [ there are duplicate keys reachable from head ]

with the data structure exactly as requested:

* `Node` (= `Ref`) is a type; `key : Node → Nat` and `next : Node → Node` are
  **map-valued program variables**; `head`, `curr`, `prev`, `n` are variables
  of type `Node` only; `y` is a `Nat` variable.
* Pre- and postconditions talk about an **arbitrary** list: the length `m`,
  the node addresses `a : Nat → Ref` and the keys `k₀ : Nat → Nat` are
  parameters, constrained only by "the heap realises this chain".

## The program (C++ reading)

    curr = head; prev = NIL;
    while (curr != NIL && key[curr] <= y) {        // BUG: should be <
      prev = curr; curr = next[curr];
    }
    if (curr != NIL && key[curr] == y) return;     // y already present
    n = new Node; key[n] = y; next[n] = curr;
    if (prev == NIL) head = n; else next[prev] = n;

The "already present?" check is what makes `≤` the culprit.  With the
correct `<` the scan stops ON the first node whose key is `≥ y`; on a sorted
list that node carries `y` whenever `y` occurs, the check fires and nothing is
inserted.  With the buggy `≤` the scan walks PAST every node carrying `y`: at
the check, `curr` is NULL or carries a key `> y`, so the check is always
false and a second node with key `y` is spliced in.

## How the informal spec is formalised (important IL subtlety)

An incorrectness triple `[P] c [Q]` claims that *every* state in `Q` is
reachable, so in IL a postcondition may only be *shrunk*, never enlarged.  The
literal post "duplicate keys `y` are reachable" is too big to be reachable in
that sense: e.g. the list `3 → 3 → 1` with `y = 3` has two reachable nodes
with key `3`, but no run produces it (the node inserted by the program is
always followed by NULL or by a key `> y`).  So the machine-checked statement
is the standard IL shape:

1. `insert_triple` / `insert_triple_front` — the exact families of result
   states `Post …` (the scan passed `p ≥ 1` nodes; the new node is linked in
   after node `p-1`) and `PostFront …` (the scan stopped at the head; the new
   node becomes the head) are reachable from the family of pre-states `Pre …`;
2. `pre_hasKey` — every `Pre` state satisfies the advisor's precondition
   "∃ n reachable from head, key n = y";
3. `post_dup` / `post_dup_front` — every state of either family satisfies the
   advisor's postcondition "duplicate keys reachable from head";
4. `insert_triple_any` packages both cases into the single triple
   `[PreAny y] insert [PostAny y]` (IL disjunction rule), and
   `insert_triple_hasKey` restates it with the advisor's precondition
   `hasKey y` *verbatim* (IL allows enlarging the precondition);
5. `insert_bug_witness` / `insert_front_witness` — both families are
   non-empty: concrete runs exhibit the duplicate end to end.

Together: the buggy insert really reaches duplicate-key states from
"y already in the list" states — for lists of any length, any addresses and
any keys.

**Sortedness.**  `Pre` does not require the list to be sorted (the advisor's
precondition does not either).  This matters for the front case: `p = 0`
means `y < key[head]`, which together with "`y` occurs in the list" is only
possible in an *unsorted* list.  There the duplicate is caused by the missing
sortedness, not by the `≤` bug: the correct `<` scan also stops at the head.
On sorted lists only the `p ≥ 1` case arises, and there the duplicate is due
to `≤`.  (That the `<` version never duplicates on sorted lists is a
correctness, i.e. Hoare-logic, statement; IL cannot express it and it is not
proved here.)
-/

namespace MapLang.LinkedList

/-- The `Node` type: a node is identified by its address. -/
abbrev Node := Ref

-- ------------------------------------------------------------
-- Program variables (typed)
-- ------------------------------------------------------------

def head : Var .ref := ⟨"head"⟩
def curr : Var .ref := ⟨"curr"⟩
def prev : Var .ref := ⟨"prev"⟩
def n    : Var .ref := ⟨"n"⟩
def y    : Var .nat := ⟨"y"⟩
/-- `key : Node → Nat` — the data array. -/
def key  : Var (.map .ref .nat) := ⟨"key"⟩
/-- `next : Node → Node` — the address array. -/
def next : Var (.map .ref .ref) := ⟨"next"⟩

-- ------------------------------------------------------------
-- Reachability and the two informal specifications
-- ------------------------------------------------------------

/-- Follow `nx` for `k` steps. -/
def iter (nx : Ref → Ref) : Nat → Ref → Ref
  | 0,     r => r
  | k + 1, r => nx (iter nx k r)

/-- `r` is reachable from `head` along `next` in state `s`. -/
def reach (s : State) (r : Node) : Prop :=
  ∃ k, iter (s⟦next⟧) k (s⟦head⟧) = r

/-- Advisor's precondition: some node reachable from head carries key `v`. -/
def hasKey (v : Nat) (s : State) : Prop :=
  ∃ r : Node, reach s r ∧ s⟦key⟧ r = v

/-- Advisor's postcondition: two distinct reachable nodes carry the same key `v`. -/
def hasDupKey (v : Nat) (t : State) : Prop :=
  ∃ r₁ r₂ : Node, r₁ ≠ r₂ ∧ reach t r₁ ∧ reach t r₂ ∧ t⟦key⟧ r₁ = v ∧ t⟦key⟧ r₂ = v

-- ------------------------------------------------------------
-- The buggy program
-- ------------------------------------------------------------

/-- Scan guard `curr ≠ NULL ∧ key[curr] ≤ y`.  **BUG:** should be `<`. -/
def G : State → Prop := fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) ≤ s⟦y⟧

/-- Loop body `prev := curr; curr := next[curr]`. -/
def Bdy : Stmt :=
  Stmt.assign prev (fun s => s⟦curr⟧);
  Stmt.assign curr (fun s => s⟦next⟧ (s⟦curr⟧))

/-- Duplicate check `curr ≠ NULL ∧ key[curr] = y`, the C++ line
    `if (curr != NIL && key[curr] == y) return;`. -/
def Found : State → Prop := fun s => s⟦curr⟧ ≠ Ref.null ∧ s⟦key⟧ (s⟦curr⟧) = s⟦y⟧

/-- Phase 1, the scan:

      curr := head; prev := NULL;
      while (curr ≠ NULL ∧ key[curr] ≤ y) { prev := curr; curr := next[curr] } -/
def Scan : Stmt :=
  Stmt.assign curr (fun s => s⟦head⟧);
  Stmt.assign prev (fun _ => Ref.null);
  Stmt.whileDo G Bdy

/-- Phase 2, allocation and splice:

      n := new; key[n] := y; next[n] := curr;
      if prev = NULL then head := n else next[prev] := n -/
def Splice : Stmt :=
  Stmt.alloc n;
  Stmt.mapUpdate key (fun s => s⟦n⟧) (fun s => s⟦y⟧);
  Stmt.mapUpdate next (fun s => s⟦n⟧) (fun s => s⟦curr⟧);
  Stmt.ifThenElse (fun s => s⟦prev⟧ = Ref.null)
    (Stmt.assign head (fun s => s⟦n⟧))
    (Stmt.mapUpdate next (fun s => s⟦prev⟧) (fun s => s⟦n⟧))

/-- Sorted-list insert with the buggy `≤` scan and the "already present?"
    check:

      Scan;
      if (curr ≠ NULL ∧ key[curr] = y) then skip else Splice -/
def insertProg : Stmt :=
  Scan;
  Stmt.ifThenElse Found Stmt.skip Splice

-- ------------------------------------------------------------
-- Describing an arbitrary chain
-- ------------------------------------------------------------

/-- Original successor of node `i`: the next node, or NULL at the end. -/
def origNext (m : Nat) (a : Nat → Ref) (i : Nat) : Ref :=
  if i + 1 < m then a (i + 1) else Ref.null

/-- Scan position after `i` steps: node `i`, or NULL once past the end. -/
def cur (m : Nat) (a : Nat → Ref) (i : Nat) : Ref :=
  if i < m then a i else Ref.null

/-- Value of `prev` after `i` scan steps: NULL at the start, then node `i-1`. -/
def prevAt (a : Nat → Ref) (i : Nat) : Ref :=
  if i = 0 then Ref.null else a (i - 1)

theorem origNext_lt {m : Nat} {a : Nat → Ref} {i : Nat} (h : i + 1 < m) :
    origNext m a i = a (i + 1) := by simp [origNext, h]
theorem cur_lt {m : Nat} {a : Nat → Ref} {i : Nat} (h : i < m) : cur m a i = a i := by
  simp [cur, h]
theorem cur_ge {m : Nat} {a : Nat → Ref} {i : Nat} (h : ¬ i < m) : cur m a i = Ref.null := by
  simp [cur, h]
theorem origNext_eq_cur {m : Nat} {a : Nat → Ref} {i : Nat} :
    origNext m a i = cur m a (i + 1) := rfl
@[simp] theorem prevAt_zero {a : Nat → Ref} : prevAt a 0 = Ref.null := rfl
@[simp] theorem prevAt_succ {a : Nat → Ref} {i : Nat} : prevAt a (i + 1) = a i := rfl

/-- The keys of the chain are `k₀ 0, …, k₀ (m-1)`. -/
def keysAt (m : Nat) (a : Nat → Ref) (k₀ : Nat → Nat) (s : State) : Prop :=
  ∀ i, i < m → s⟦key⟧ (a i) = k₀ i
/-- The links of the chain: `next (a i) = a (i+1)`, NULL at the end. -/
def linksAt (m : Nat) (a : Nat → Ref) (s : State) : Prop :=
  ∀ i, i < m → s⟦next⟧ (a i) = origNext m a i
/-- All chain nodes are allocated. -/
def allocAt (m : Nat) (a : Nat → Ref) (s : State) : Prop :=
  ∀ i, i < m → s.alloc (a i) = true

/-- **Precondition family** (arbitrary list): `head` at the start of the chain,
    variable `y = yv`, heap realising the chain.  Everything else is free. -/
def Pre (m : Nat) (a : Nat → Ref) (k₀ : Nat → Nat) (yv : Nat) (s : State) : Prop :=
  s⟦head⟧ = a 0 ∧ s⟦y⟧ = yv ∧ keysAt m a k₀ s ∧ linksAt m a s ∧ allocAt m a s

/-- **Postcondition family, middle/end insertion** (`p ≥ 1`): the scan stopped
    at position `p`, the fresh node `r` carries `yv`, and it is spliced after
    node `p-1`. -/
def Post (m p : Nat) (a : Nat → Ref) (k₀ : Nat → Nat) (yv : Nat) (r : Ref) (t : State) : Prop :=
  t⟦head⟧ = a 0 ∧ t⟦y⟧ = yv ∧
  t⟦curr⟧ = cur m a p ∧ t⟦prev⟧ = a (p - 1) ∧ t⟦n⟧ = r ∧
  r ≠ Ref.null ∧ (∀ i, i < m → a i ≠ r) ∧ t.alloc r = true ∧ allocAt m a t ∧
  t⟦key⟧ r = yv ∧ t⟦next⟧ r = cur m a p ∧
  keysAt m a k₀ t ∧
  t⟦next⟧ (a (p - 1)) = r ∧ (∀ i, i < m → i ≠ p - 1 → t⟦next⟧ (a i) = origNext m a i)

/-- **Postcondition family, front insertion** (`p = 0`): the scan stopped at
    the head, the fresh node `r` carries `yv`, points to the old head and is
    the new head; the old chain is untouched. -/
def PostFront (m : Nat) (a : Nat → Ref) (k₀ : Nat → Nat) (yv : Nat) (r : Ref) (t : State) :
    Prop :=
  t⟦head⟧ = r ∧ t⟦y⟧ = yv ∧
  t⟦curr⟧ = a 0 ∧ t⟦prev⟧ = Ref.null ∧ t⟦n⟧ = r ∧
  r ≠ Ref.null ∧ (∀ i, i < m → a i ≠ r) ∧ t.alloc r = true ∧ allocAt m a t ∧
  t⟦key⟧ r = yv ∧ t⟦next⟧ r = a 0 ∧
  keysAt m a k₀ t ∧ linksAt m a t

-- ------------------------------------------------------------
-- Forward execution from any state realising the chain
-- ------------------------------------------------------------

/-- The state after `i` scan iterations started in `σ`: only `curr` and
    `prev` have moved. -/
def scanSt (m : Nat) (a : Nat → Ref) (σ : State) (i : Nat) : State :=
  (σ[curr ↦ cur m a i])[prev ↦ prevAt a i]

/-- The state after `n := new; key[n] := y; next[n] := curr`, the fresh node
    being `r`. -/
def linkSt (m p : Nat) (a : Nat → Ref) (yv : Nat) (r : Ref) (σ : State) : State :=
  (((scanSt m a σ p).doAlloc n r).mapUpd key r yv).mapUpd next r (cur m a p)

/-- The final state: the fresh node becomes the new head (`p = 0`) or is
    linked in after node `p-1`. -/
def finalSt (m p : Nat) (a : Nat → Ref) (yv : Nat) (r : Ref) (σ : State) : State :=
  if p = 0 then (linkSt m p a yv r σ)[head ↦ r]
  else (linkSt m p a yv r σ).mapUpd next (a (p - 1)) r

section ScanLemmas
variable {m i : Nat} {a : Nat → Ref} {σ : State}

@[simp] theorem scanSt_head : (scanSt m a σ i)⟦head⟧ = σ⟦head⟧ := by simp [scanSt]
@[simp] theorem scanSt_n : (scanSt m a σ i)⟦n⟧ = σ⟦n⟧ := by simp [scanSt]
@[simp] theorem scanSt_y : (scanSt m a σ i)⟦y⟧ = σ⟦y⟧ := by simp [scanSt]
@[simp] theorem scanSt_key : (scanSt m a σ i)⟦key⟧ = σ⟦key⟧ := by simp [scanSt]
@[simp] theorem scanSt_next : (scanSt m a σ i)⟦next⟧ = σ⟦next⟧ := by simp [scanSt]
@[simp] theorem scanSt_curr : (scanSt m a σ i)⟦curr⟧ = cur m a i := by simp [scanSt]
@[simp] theorem scanSt_prev : (scanSt m a σ i)⟦prev⟧ = prevAt a i := by simp [scanSt]
@[simp] theorem scanSt_alloc : (scanSt m a σ i).alloc = σ.alloc := rfl

end ScanLemmas

/-- One loop iteration moves the scan from node `i` to node `i+1`. -/
theorem scan_body {m i : Nat} {a : Nat → Ref} {σ : State}
    (hlinks : linksAt m a σ) (him : i < m) :
    (Bdy, scanSt m a σ i) ⟹ scanSt m a σ (i + 1) := by
  have hc : (scanSt m a σ i)⟦curr⟧ = a i := by rw [scanSt_curr, cur_lt him]
  have hnx : ((scanSt m a σ i)[prev ↦ a i])⟦next⟧ (((scanSt m a σ i)[prev ↦ a i])⟦curr⟧)
      = cur m a (i + 1) := by
    have h : σ.vars (.map .ref .ref) next.name (a i) = cur m a (i + 1) := by
      rw [← origNext_eq_cur]; exact hlinks i him
    simp [cur_lt him, h]
  refine BigStep.seq _ _ _ _ _ (BigStep.assign _ _ _) ((BigStep.assign _ _ _).cast ?_)
  simp only [hc]
  rw [hnx]
  unfold scanSt
  rw [State.update_update,
      State.update_comm (σ[curr ↦ cur m a i]) prev curr (a i) (cur m a (i + 1))
        (Or.inr (by decide)),
      State.update_update, prevAt_succ]

/-- **The scan.**  From any state realising the chain, with the stop position
    `p` characterised by `hple` (keys before `p` are `≤ yv`) and `hpgt` (the
    key at `p`, if any, is `> yv`), the scan ends in `scanSt … p`. -/
theorem scan_exec {m p yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {σ : State}
    (hm : 0 < m) (hpm : p ≤ m)
    (hple : ∀ i, i < p → k₀ i ≤ yv) (hpgt : p < m → yv < k₀ p)
    (hnn : ∀ i, i < m → a i ≠ Ref.null)
    (hhead : σ⟦head⟧ = a 0) (hy : σ⟦y⟧ = yv)
    (hkeys : keysAt m a k₀ σ) (hlinks : linksAt m a σ) :
    (Scan, σ) ⟹ scanSt m a σ p := by
  have hy' : σ.vars .nat y.name = yv := hy
  -- ▸ The guard holds while i < p …
  have hGtrue : ∀ i, i < p → G (scanSt m a σ i) := by
    intro i hip
    have him : i < m := by omega
    unfold G
    simp only [State.get, scanSt_curr, scanSt_key, scanSt_y]
    rw [cur_lt him]
    refine ⟨hnn i him, ?_⟩
    have h1 : σ.vars (.map .ref .nat) key.name (a i) = k₀ i := hkeys i him
    rw [h1, hy']
    exact hple i hip
  -- ▸ … and fails at p.
  have hGfalse : ¬ G (scanSt m a σ p) := by
    unfold G
    rintro ⟨hne, hle⟩
    simp only [State.get, scanSt_curr, scanSt_key, scanSt_y] at hne hle
    by_cases hpltm : p < m
    · rw [cur_lt hpltm] at hle
      have h1 : σ.vars (.map .ref .nat) key.name (a p) = k₀ p := hkeys p hpltm
      rw [h1, hy'] at hle
      have hle' : k₀ p ≤ yv := hle
      have := hpgt hpltm
      omega
    · rw [cur_ge hpltm] at hne
      exact hne rfl
  -- ▸ The loop: scanSt i →* scanSt p.
  have hwalk : ∀ k i, i + k = p →
      (Stmt.whileDo G Bdy, scanSt m a σ i) ⟹ scanSt m a σ p := by
    intro k
    induction k with
    | zero =>
      intro i hi
      have : i = p := by omega
      subst this
      exact BigStep.while_false _ _ _ hGfalse
    | succ k ih =>
      intro i hi
      have hip : i < p := by omega
      exact BigStep.while_true _ _ _ _ _ (hGtrue i hip) (scan_body hlinks (by omega))
        (ih (i + 1) (by omega))
  -- ▸ `curr := head; prev := NULL` reaches scanSt 0.
  have hinit : (σ[curr ↦ σ⟦head⟧])[prev ↦ Ref.null] = scanSt m a σ 0 := by
    unfold scanSt
    rw [cur_lt hm, hhead, prevAt_zero]
  refine BigStep.seq _ _ _ _ _ (BigStep.assign _ _ _) ?_
  refine BigStep.seq _ _ _ _ _ ((BigStep.assign _ _ _).cast hinit) ?_
  exact hwalk p 0 (by omega)

/-- **Forward execution of the whole insert.**  From any state `σ` realising
    the chain, if the scan stops at `p` and `r` is a fresh non-NULL node, the
    program runs to `finalSt m p a yv r σ`.  In particular the duplicate check
    is always FALSE after the buggy scan: `curr` is NULL or carries a key
    `> yv`. -/
theorem insert_exec {m p yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {r : Ref} {σ : State}
    (hm : 0 < m) (hpm : p ≤ m)
    (hple : ∀ i, i < p → k₀ i ≤ yv) (hpgt : p < m → yv < k₀ p)
    (hnn : ∀ i, i < m → a i ≠ Ref.null)
    (hhead : σ⟦head⟧ = a 0) (hy : σ⟦y⟧ = yv)
    (hkeys : keysAt m a k₀ σ) (hlinks : linksAt m a σ)
    (hfresh : σ.alloc r = false) (hrnn : r ≠ Ref.null) :
    (insertProg, σ) ⟹ finalSt m p a yv r σ := by
  have hy' : σ.vars .nat y.name = yv := hy
  -- ▸ The duplicate check fails after the scan.
  have hnotFound : ¬ Found (scanSt m a σ p) := by
    unfold Found
    rintro ⟨hne, heq⟩
    simp only [State.get, scanSt_curr, scanSt_key, scanSt_y] at hne heq
    by_cases hpltm : p < m
    · rw [cur_lt hpltm] at heq
      have h1 : σ.vars (.map .ref .nat) key.name (a p) = k₀ p := hkeys p hpltm
      rw [h1, hy'] at heq
      have heq' : k₀ p = yv := heq
      have := hpgt hpltm
      omega
    · rw [cur_ge hpltm] at hne
      exact hne rfl
  -- ▸ Values read by the splice.
  have hfresh' : (scanSt m a σ p).alloc r = false := by rw [scanSt_alloc]; exact hfresh
  have hA_n : ((scanSt m a σ p).doAlloc n r)⟦n⟧ = r := by simp
  have hA_y : ((scanSt m a σ p).doAlloc n r)⟦y⟧ = yv := by simp [hy']
  have h1_n : (((scanSt m a σ p).doAlloc n r).mapUpd key r yv)⟦n⟧ = r := by simp
  have h1_curr : (((scanSt m a σ p).doAlloc n r).mapUpd key r yv)⟦curr⟧ = cur m a p := by
    simp
  have h2_prev : (linkSt m p a yv r σ)⟦prev⟧ = prevAt a p := by simp [linkSt]
  have h2_n : (linkSt m p a yv r σ)⟦n⟧ = r := by simp [linkSt]
  -- ▸ Assemble the derivation.
  refine BigStep.seq _ _ _ _ _ (scan_exec hm hpm hple hpgt hnn hhead hy hkeys hlinks) ?_
  refine BigStep.if_false _ _ _ _ _ hnotFound ?_
  refine BigStep.seq _ _ _ _ _ (BigStep.alloc n r _ hfresh' hrnn) ?_
  refine BigStep.seq _ _ _ _ _ ((BigStep.mapUpdate _ _ _ _).cast (by rw [hA_n, hA_y])) ?_
  refine BigStep.seq _ _ _ _ _ ((BigStep.mapUpdate _ _ _ _).cast (by rw [h1_n, h1_curr])) ?_
  by_cases hp : p = 0
  · -- `prev = NULL`: the fresh node becomes the head.
    subst hp
    refine BigStep.if_true _ _ _ _ _ ?_ ((BigStep.assign _ _ _).cast ?_)
    · show (linkSt m 0 a yv r σ)⟦prev⟧ = Ref.null
      rw [h2_prev, prevAt_zero]
    · show (linkSt m 0 a yv r σ)[head ↦ (linkSt m 0 a yv r σ)⟦n⟧] = finalSt m 0 a yv r σ
      rw [h2_n]
      simp only [finalSt, ↓reduceIte]
  · -- `prev = node p-1`: splice after it.
    have hprev : prevAt a p = a (p - 1) := by simp [prevAt, hp]
    refine BigStep.if_false _ _ _ _ _ ?_ ((BigStep.mapUpdate _ _ _ _).cast ?_)
    · show ¬ (linkSt m p a yv r σ)⟦prev⟧ = Ref.null
      rw [h2_prev, hprev]
      exact hnn (p - 1) (by omega)
    · show (linkSt m p a yv r σ).mapUpd next ((linkSt m p a yv r σ)⟦prev⟧)
          ((linkSt m p a yv r σ)⟦n⟧) = finalSt m p a yv r σ
      rw [h2_prev, h2_n, hprev]
      simp only [finalSt, hp, ↓reduceIte]

-- ------------------------------------------------------------
-- Witness pre-states (read backwards off a post-state)
-- ------------------------------------------------------------

/-- Pre-state for the middle/end case: un-splice node `p-1` and un-allocate
    the fresh node `r`.  Every other slot is exactly `t`'s. -/
def preSt (m p : Nat) (a : Nat → Ref) (r : Ref) (t : State) : State :=
  { vars  := (t.mapUpd next (a (p - 1)) (origNext m a (p - 1))).vars
    alloc := fun q => if q = r then false else t.alloc q }

/-- Pre-state for the front case: restore the old head and un-allocate the
    fresh node `r`.  Every other slot is exactly `t`'s. -/
def preStFront (a : Nat → Ref) (r : Ref) (t : State) : State :=
  { vars  := (t[head ↦ a 0]).vars
    alloc := fun q => if q = r then false else t.alloc q }

section WitnessLemmas
variable {m p : Nat} {a : Nat → Ref} {r q : Ref} {t : State}

@[simp] theorem preSt_head : (preSt m p a r t)⟦head⟧ = t⟦head⟧ := by simp [preSt]
@[simp] theorem preSt_curr : (preSt m p a r t)⟦curr⟧ = t⟦curr⟧ := by simp [preSt]
@[simp] theorem preSt_prev : (preSt m p a r t)⟦prev⟧ = t⟦prev⟧ := by simp [preSt]
@[simp] theorem preSt_n : (preSt m p a r t)⟦n⟧ = t⟦n⟧ := by simp [preSt]
@[simp] theorem preSt_y : (preSt m p a r t)⟦y⟧ = t⟦y⟧ := by simp [preSt]
@[simp] theorem preSt_key : (preSt m p a r t)⟦key⟧ = t⟦key⟧ := by simp [preSt]
theorem preSt_next :
    (preSt m p a r t)⟦next⟧ q = if q = a (p - 1) then origNext m a (p - 1) else t⟦next⟧ q := by
  simp [preSt]
@[simp] theorem preSt_alloc : (preSt m p a r t).alloc q = if q = r then false else t.alloc q :=
  rfl

@[simp] theorem preStFront_head : (preStFront a r t)⟦head⟧ = a 0 := by simp [preStFront]
@[simp] theorem preStFront_curr : (preStFront a r t)⟦curr⟧ = t⟦curr⟧ := by simp [preStFront]
@[simp] theorem preStFront_prev : (preStFront a r t)⟦prev⟧ = t⟦prev⟧ := by simp [preStFront]
@[simp] theorem preStFront_n : (preStFront a r t)⟦n⟧ = t⟦n⟧ := by simp [preStFront]
@[simp] theorem preStFront_y : (preStFront a r t)⟦y⟧ = t⟦y⟧ := by simp [preStFront]
@[simp] theorem preStFront_key : (preStFront a r t)⟦key⟧ = t⟦key⟧ := by simp [preStFront]
@[simp] theorem preStFront_next : (preStFront a r t)⟦next⟧ = t⟦next⟧ := by simp [preStFront]
@[simp] theorem preStFront_alloc :
    (preStFront a r t).alloc q = if q = r then false else t.alloc q := rfl

end WitnessLemmas

/-- Running the insert from `preSt` lands exactly on the `Post` state `t`. -/
theorem finalSt_preSt {m p yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {r : Ref} {t : State}
    (hp0 : 0 < p) (hpost : Post m p a k₀ yv r t) :
    finalSt m p a yv r (preSt m p a r t) = t := by
  obtain ⟨_, _, hcurr, hprev, hn, _, _, hallocr, _, hkeyr, hnextr, _, hnextP, _⟩ := hpost
  simp only [State.get] at hcurr hprev hn hkeyr hnextr hnextP
  have hp0' : ¬ p = 0 := by omega
  have hprevAt : prevAt a p = a (p - 1) := by simp [prevAt, hp0']
  refine State.ext' (fun τ z => ?_) (fun q => ?_)
  · by_cases hτ : τ = .ref
    · subst hτ
      by_cases h1 : z = n.name
      · subst h1
        simp [finalSt, linkSt, hp0', hn]
      · by_cases h2 : z = curr.name
        · subst h2
          simp [finalSt, linkSt, hp0', hcurr]
        · by_cases h3 : z = prev.name
          · subst h3
            simp [finalSt, linkSt, hp0', hprevAt, hprev]
          · simp [finalSt, linkSt, scanSt, preSt, hp0', h1, h2, h3]
    · by_cases hτ2 : τ = .map .ref .nat
      · subst hτ2
        by_cases hk : z = key.name
        · subst hk
          funext q
          by_cases hq : q = r
          · subst hq
            simp [finalSt, linkSt, hp0', hkeyr]
          · simp [finalSt, linkSt, hp0', hq]
        · simp [finalSt, linkSt, scanSt, preSt, hp0', hk]
      · by_cases hτ3 : τ = .map .ref .ref
        · subst hτ3
          by_cases hnx : z = next.name
          · subst hnx
            funext q
            by_cases hq1 : q = a (p - 1)
            · subst hq1
              simp [finalSt, linkSt, hp0', hnextP]
            · by_cases hq2 : q = r
              · subst hq2
                simp [finalSt, linkSt, hp0', hq1, hnextr]
              · simp [finalSt, linkSt, preSt_next, hp0', hq1, hq2]
          · simp [finalSt, linkSt, scanSt, preSt, hp0', hnx]
        · simp [finalSt, linkSt, scanSt, preSt, hp0', hτ, hτ2, hτ3]
  · by_cases hq : q = r
    · subst hq
      simp [finalSt, linkSt, hp0', hallocr]
    · simp [finalSt, linkSt, hp0', hq]

/-- Running the insert from `preStFront` lands exactly on the `PostFront`
    state `t`. -/
theorem finalSt_preStFront {m yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {r : Ref}
    {t : State} (hm : 0 < m) (hpost : PostFront m a k₀ yv r t) :
    finalSt m 0 a yv r (preStFront a r t) = t := by
  obtain ⟨hhead, _, hcurr, hprev, hn, _, _, hallocr, _, hkeyr, hnextr, _, _⟩ := hpost
  simp only [State.get] at hhead hcurr hprev hn hkeyr hnextr
  have hc0 : cur m a 0 = a 0 := cur_lt hm
  refine State.ext' (fun τ z => ?_) (fun q => ?_)
  · by_cases hτ : τ = .ref
    · subst hτ
      by_cases h0 : z = head.name
      · subst h0
        simp [finalSt, hhead]
      · by_cases h1 : z = n.name
        · subst h1
          simp [finalSt, linkSt, hn]
        · by_cases h2 : z = curr.name
          · subst h2
            simp [finalSt, linkSt, hc0, hcurr]
          · by_cases h3 : z = prev.name
            · subst h3
              simp [finalSt, linkSt, hprev]
            · simp [finalSt, linkSt, scanSt, preStFront, h0, h1, h2, h3]
    · by_cases hτ2 : τ = .map .ref .nat
      · subst hτ2
        by_cases hk : z = key.name
        · subst hk
          funext q
          by_cases hq : q = r
          · subst hq
            simp [finalSt, linkSt, hkeyr]
          · simp [finalSt, linkSt, hq]
        · simp [finalSt, linkSt, scanSt, preStFront, hk]
      · by_cases hτ3 : τ = .map .ref .ref
        · subst hτ3
          by_cases hnx : z = next.name
          · subst hnx
            funext q
            by_cases hq : q = r
            · subst hq
              simp [finalSt, linkSt, hc0, hnextr]
            · simp [finalSt, linkSt, hq]
          · simp [finalSt, linkSt, scanSt, preStFront, hnx]
        · simp [finalSt, linkSt, scanSt, preStFront, hτ, hτ2, hτ3]
  · by_cases hq : q = r
    · subst hq
      simp [finalSt, linkSt, hallocr]
    · simp [finalSt, linkSt, hq]

-- ------------------------------------------------------------
-- MAIN THEOREMS: the insert triples on an arbitrary list
-- ------------------------------------------------------------

/-- **The advisor's example, machine-checked (middle/end insertion).**  For a
    list of arbitrary length `m`, addresses `a` and keys `k₀`, if the buggy
    scan stops at position `p ≥ 1` (characterised by `hple`/`hpgt`), then
    EVERY state of `Post m p a k₀ yv r` is reachable from a state of
    `Pre m a k₀ yv`. -/
theorem insert_triple {m p yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {r : Ref}
    (hm : 0 < m) (hp0 : 0 < p) (hpm : p ≤ m)
    (hple : ∀ i, i < p → k₀ i ≤ yv)
    (hpgt : p < m → yv < k₀ p)
    (hdist : ∀ i l, i < m → l < m → a i = a l → i = l)
    (hnn : ∀ i, i < m → a i ≠ Ref.null) :
    [* Pre m a k₀ yv *] (insertProg) [* Post m p a k₀ yv r *] := by
  intro t hpost
  have hfinal := finalSt_preSt hp0 hpost
  obtain ⟨hhead, hy, _, _, _, hrnn, hroff, _, hallocA, _, _, hkeys, _, hnexts⟩ := hpost
  have hpm' : p - 1 < m := by omega
  -- ▸ The witness pre-state realises the chain.
  have hhead0 : (preSt m p a r t)⟦head⟧ = a 0 := by rw [preSt_head]; exact hhead
  have hy0 : (preSt m p a r t)⟦y⟧ = yv := by rw [preSt_y]; exact hy
  have hkeys0 : keysAt m a k₀ (preSt m p a r t) := by
    intro i hi; rw [preSt_key]; exact hkeys i hi
  have hlinks0 : linksAt m a (preSt m p a r t) := by
    intro i hi
    rw [preSt_next]
    by_cases hip : a i = a (p - 1)
    · have hi' : i = p - 1 := hdist i (p - 1) hi hpm' hip
      subst hi'; simp
    · simp only [hip, ↓reduceIte]
      exact hnexts i hi (fun e => hip (by rw [e]))
  have halloc0 : allocAt m a (preSt m p a r t) := by
    intro i hi
    rw [preSt_alloc]
    simp only [hroff i hi, ↓reduceIte]
    exact hallocA i hi
  have hfresh : (preSt m p a r t).alloc r = false := by simp
  exact ⟨preSt m p a r t, ⟨hhead0, hy0, hkeys0, hlinks0, halloc0⟩,
    (insert_exec hm hpm hple hpgt hnn hhead0 hy0 hkeys0 hlinks0 hfresh hrnn).cast hfinal⟩

/-- **Front insertion** (`p = 0`): the scan stops at the head because
    `yv < key[head]`; `prev` stays NULL and `head := n`.  EVERY state of
    `PostFront m a k₀ yv r` is reachable from a state of `Pre m a k₀ yv`. -/
theorem insert_triple_front {m yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {r : Ref}
    (hm : 0 < m) (hpgt : yv < k₀ 0)
    (hnn : ∀ i, i < m → a i ≠ Ref.null) :
    [* Pre m a k₀ yv *] (insertProg) [* PostFront m a k₀ yv r *] := by
  intro t hpost
  have hfinal := finalSt_preStFront hm hpost
  obtain ⟨_, hy, _, _, _, hrnn, hroff, _, hallocA, _, _, hkeys, hlinks⟩ := hpost
  -- ▸ The witness pre-state realises the chain.
  have hhead0 : (preStFront a r t)⟦head⟧ = a 0 := preStFront_head
  have hy0 : (preStFront a r t)⟦y⟧ = yv := by rw [preStFront_y]; exact hy
  have hkeys0 : keysAt m a k₀ (preStFront a r t) := by
    intro i hi; rw [preStFront_key]; exact hkeys i hi
  have hlinks0 : linksAt m a (preStFront a r t) := by
    intro i hi; rw [preStFront_next]; exact hlinks i hi
  have halloc0 : allocAt m a (preStFront a r t) := by
    intro i hi
    rw [preStFront_alloc]
    simp only [hroff i hi, ↓reduceIte]
    exact hallocA i hi
  have hfresh : (preStFront a r t).alloc r = false := by simp
  exact ⟨preStFront a r t, ⟨hhead0, hy0, hkeys0, hlinks0, halloc0⟩,
    (insert_exec (p := 0) hm (Nat.zero_le _) (fun _ hi => absurd hi (Nat.not_lt_zero _))
      (fun _ => hpgt) hnn hhead0 hy0 hkeys0 hlinks0 hfresh hrnn).cast hfinal⟩

-- ------------------------------------------------------------
-- The informal specifications follow from the families
-- ------------------------------------------------------------

/-- Walking the chain from `a 0` in any state realising the links. -/
theorem pre_iter {m : Nat} {a : Nat → Ref} {s : State} (hl : linksAt m a s) :
    ∀ i, i < m → iter (s⟦next⟧) i (a 0) = a i := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hi
    simp only [iter]
    rw [ih (by omega), hl i (by omega), origNext_lt hi]

/-- Every `Pre` state satisfies the advisor's precondition
    "∃ node reachable from head whose key is `yv`", provided `yv` occurs in the list. -/
theorem pre_hasKey {m j yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {s : State}
    (hj : j < m) (hjy : k₀ j = yv) (hpre : Pre m a k₀ yv s) : hasKey yv s := by
  obtain ⟨hhead, _, hkeys, hlinks, _⟩ := hpre
  refine ⟨a j, ⟨j, ?_⟩, ?_⟩
  · rw [hhead]; exact pre_iter hlinks j hj
  · rw [hkeys j hj]; exact hjy

/-- Every `Post` state satisfies the advisor's postcondition "there are
    duplicate keys reachable from head": the old node `a j` carrying `yv` and
    the fresh node `r` are both reachable and both carry `yv`. -/
theorem post_dup {m p j yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {r : Ref}
    (hp0 : 0 < p) (hpm : p ≤ m) (hj : j < m) (hjy : k₀ j = yv) :
    ∀ t, Post m p a k₀ yv r t → hasDupKey yv t := by
  intro t hpost
  obtain ⟨hhead, _, _, _, _, _, hroff, _, _, hkeyr, hnextr, hkeys, hnextP, hnexts⟩ := hpost
  -- the first p-1 nodes are reached along the untouched links
  have hA : ∀ i, i ≤ p - 1 → iter (t⟦next⟧) i (a 0) = a i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hi
      simp only [iter]
      rw [ih (by omega), hnexts i (by omega) (by omega), origNext_lt (by omega)]
  -- step p reaches the fresh node
  have hB : iter (t⟦next⟧) p (a 0) = r := by
    have hp' : p = (p - 1) + 1 := by omega
    rw [hp']
    simp only [iter]
    rw [hA (p - 1) (Nat.le_refl _), hnextP]
  -- the rest of the chain is reached through the fresh node
  have hC : ∀ d, p + d < m → iter (t⟦next⟧) (p + d + 1) (a 0) = a (p + d) := by
    intro d
    induction d with
    | zero =>
      intro hlt
      simp only [iter]
      rw [hB, hnextr]
      exact cur_lt (by omega)
    | succ d ih =>
      intro hlt
      have hlt' : p + d < m := by omega
      have hstep : iter (t⟦next⟧) (p + (d + 1) + 1) (a 0)
          = t⟦next⟧ (iter (t⟦next⟧) (p + d + 1) (a 0)) := rfl
      have hgoal : iter (t⟦next⟧) (p + (d + 1) + 1) (a 0) = a (p + d + 1) := by
        rw [hstep, ih hlt', hnexts (p + d) hlt' (by omega)]
        exact origNext_lt (by omega)
      exact hgoal
  have hreach : ∀ q, (∃ k, iter (t⟦next⟧) k (a 0) = q) → reach t q := by
    intro q ⟨k, hk⟩
    exact ⟨k, by rw [hhead]; exact hk⟩
  have hreach_j : reach t (a j) := by
    by_cases hjp : j ≤ p - 1
    · exact hreach _ ⟨j, hA j hjp⟩
    · refine hreach _ ⟨j + 1, ?_⟩
      have hd := hC (j - p) (by omega)
      rw [show p + (j - p) = j by omega] at hd
      exact hd
  have hreach_r : reach t r := hreach _ ⟨p, hB⟩
  refine ⟨a j, r, hroff j hj, hreach_j, hreach_r, ?_, hkeyr⟩
  rw [hkeys j hj]; exact hjy

/-- Every `PostFront` state satisfies the advisor's postcondition: the fresh
    head `r` (step 0) and the old node `a j` (step `j+1`, through `r`) are
    both reachable and both carry `yv`. -/
theorem post_dup_front {m j yv : Nat} {a : Nat → Ref} {k₀ : Nat → Nat} {r : Ref}
    (hj : j < m) (hjy : k₀ j = yv) :
    ∀ t, PostFront m a k₀ yv r t → hasDupKey yv t := by
  intro t hpost
  obtain ⟨hhead, _, _, _, _, _, hroff, _, _, hkeyr, hnextr, hkeys, hlinks⟩ := hpost
  -- the old chain hangs behind the fresh head
  have hA : ∀ i, i < m → iter (t⟦next⟧) (i + 1) r = a i := by
    intro i
    induction i with
    | zero => intro _; simp only [iter]; exact hnextr
    | succ i ih =>
      intro hi
      have hstep : iter (t⟦next⟧) (i + 1 + 1) r = t⟦next⟧ (iter (t⟦next⟧) (i + 1) r) := rfl
      rw [hstep, ih (by omega), hlinks i (by omega), origNext_lt hi]
  have hreach_r : reach t r := ⟨0, by rw [hhead]; rfl⟩
  have hreach_j : reach t (a j) := ⟨j + 1, by rw [hhead]; exact hA j hj⟩
  refine ⟨a j, r, hroff j hj, hreach_j, hreach_r, ?_, hkeyr⟩
  rw [hkeys j hj]; exact hjy

-- ------------------------------------------------------------
-- The packaged triples (list existentially quantified)
-- ------------------------------------------------------------

/-- "`s` holds SOME well-formed list in which `yv` occurs" — the advisor's
    precondition with the list packaged existentially. -/
def PreAny (yv : Nat) (s : State) : Prop :=
  ∃ (m : Nat) (a : Nat → Ref) (k₀ : Nat → Nat),
    0 < m ∧ (∀ i l, i < m → l < m → a i = a l → i = l) ∧ (∀ i, i < m → a i ≠ Ref.null) ∧
    (∃ j, j < m ∧ k₀ j = yv) ∧ Pre m a k₀ yv s

/-- "`t` is the result of the buggy insert on SOME such list, the scan having
    passed at least one node" (splice after node `p-1`). -/
def PostMidAny (yv : Nat) (t : State) : Prop :=
  ∃ (m p : Nat) (a : Nat → Ref) (k₀ : Nat → Nat) (r : Ref),
    0 < m ∧ 0 < p ∧ p ≤ m ∧
    (∀ i, i < p → k₀ i ≤ yv) ∧ (p < m → yv < k₀ p) ∧
    (∀ i l, i < m → l < m → a i = a l → i = l) ∧ (∀ i, i < m → a i ≠ Ref.null) ∧
    (∃ j, j < m ∧ k₀ j = yv) ∧ Post m p a k₀ yv r t

/-- "`t` is the result of the buggy insert on SOME such list, the scan having
    stopped at the head" (new head; possible only for unsorted lists). -/
def PostFrontAny (yv : Nat) (t : State) : Prop :=
  ∃ (m : Nat) (a : Nat → Ref) (k₀ : Nat → Nat) (r : Ref),
    0 < m ∧ yv < k₀ 0 ∧
    (∀ i l, i < m → l < m → a i = a l → i = l) ∧ (∀ i, i < m → a i ≠ Ref.null) ∧
    (∃ j, j < m ∧ k₀ j = yv) ∧ PostFront m a k₀ yv r t

/-- "`t` is the result of the buggy insert on SOME such list": either case. -/
def PostAny (yv : Nat) (t : State) : Prop := PostMidAny yv t ∨ PostFrontAny yv t

theorem insert_triple_mid_any (yv : Nat) :
    [* PreAny yv *] (insertProg) [* PostMidAny yv *] := by
  rintro t ⟨m, p, a, k₀, r, hm, hp0, hpm, hple, hpgt, hdist, hnn, hj, hpost⟩
  obtain ⟨s, hs, hrun⟩ := insert_triple hm hp0 hpm hple hpgt hdist hnn t hpost
  exact ⟨s, ⟨m, a, k₀, hm, hdist, hnn, hj, hs⟩, hrun⟩

theorem insert_triple_front_any (yv : Nat) :
    [* PreAny yv *] (insertProg) [* PostFrontAny yv *] := by
  rintro t ⟨m, a, k₀, r, hm, hpgt, hdist, hnn, hj, hpost⟩
  obtain ⟨s, hs, hrun⟩ := insert_triple_front hm hpgt hnn t hpost
  exact ⟨s, ⟨m, a, k₀, hm, hdist, hnn, hj, hs⟩, hrun⟩

/-- **One triple for all lists and both insertion points**:
    `[PreAny yv] insert [PostAny yv]`, by the IL disjunction rule. -/
theorem insert_triple_any (yv : Nat) : [* PreAny yv *] (insertProg) [* PostAny yv *] :=
  disj (insert_triple_mid_any yv) (insert_triple_front_any yv)

/-- `PreAny` ⊆ "∃ n reachable from head with key n = yv". -/
theorem preAny_hasKey {yv : Nat} {s : State} (h : PreAny yv s) : hasKey yv s := by
  obtain ⟨m, a, k₀, _, _, _, ⟨j, hj, hjy⟩, hpre⟩ := h
  exact pre_hasKey hj hjy hpre

/-- `PostAny` ⊆ "there are duplicate keys reachable from head". -/
theorem postAny_dup {yv : Nat} {t : State} (h : PostAny yv t) : hasDupKey yv t := by
  rcases h with ⟨m, p, a, k₀, r, _, hp0, hpm, _, _, _, _, ⟨j, hj, hjy⟩, hpost⟩ |
                ⟨m, a, k₀, r, _, _, _, _, ⟨j, hj, hjy⟩, hpost⟩
  · exact post_dup hp0 hpm hj hjy t hpost
  · exact post_dup_front hj hjy t hpost

/-- **The advisor's triple with the precondition verbatim.**

    In IL the precondition may be *enlarged*: a state reached from some
    `PreAny` state is also reached from some `hasKey` state, because
    `PreAny ⊆ hasKey` (`preAny_hasKey`).  So the `consequence` rule turns
    `insert_triple_any` into a triple whose precondition is literally the
    advisor's `hasKey y`.

    The postcondition cannot be treated the same way.  IL only allows it to
    be *shrunk*, since `[P] c [Q]` promises that EVERY state of `Q` is
    reachable.  The advisor's postcondition "duplicate keys are reachable
    from head" (`hasDupKey y`) contains unreachable states (e.g. the list
    `3 → 3 → 1` with `y = 3`), so it is not a valid IL postcondition for
    this program.  The formal statement therefore keeps the reachable family
    `PostAny y` and records the advisor's reading as the inclusion
    `PostAny y ⊆ hasDupKey y` (`postAny_dup`). -/
theorem insert_triple_hasKey (yv : Nat) :
    [* hasKey yv *] (insertProg) [* PostAny yv *] :=
  consequence (fun _ h => preAny_hasKey h) (insert_triple_any yv) (fun _ h => h)

-- ------------------------------------------------------------
-- Non-emptiness: a concrete run of the bug (list 1 → 3, insert 3)
-- ------------------------------------------------------------

/-- Concrete bug state: the list `1 → 3 → 3` (nodes ⟨1⟩, ⟨2⟩ and the fresh
    node ⟨3⟩ spliced after ⟨2⟩), with `y = 3`. -/
def t₀ : State :=
  { vars := fun τ x =>
      match τ with
      | .ref => if x = "head" then ⟨1⟩ else if x = "curr" then Ref.null
                else if x = "prev" then ⟨2⟩ else if x = "n" then ⟨3⟩ else Ref.null
      | .nat => if x = "y" then 3 else 0
      | .map .ref .nat => fun q => if q = ⟨1⟩ then 1 else if q = ⟨2⟩ then 3
                                   else if q = ⟨3⟩ then 3 else 0
      | .map .ref .ref => fun q => if q = ⟨1⟩ then ⟨2⟩ else if q = ⟨2⟩ then ⟨3⟩ else Ref.null
      | τ => τ.default
    alloc := fun q => decide (1 ≤ q.addr ∧ q.addr ≤ 3) }

theorem t₀_post : Post 2 2 (fun i => ⟨i + 1⟩) (fun i => 2 * i + 1) 3 ⟨3⟩ t₀ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro i hi; rcases i with _ | _ | i
    · decide
    · decide
    · omega
  · decide
  · intro i hi; rcases i with _ | _ | i
    · decide
    · decide
    · omega
  · decide
  · decide
  · intro i hi; rcases i with _ | _ | i
    · decide
    · decide
    · omega
  · decide
  · intro i hi hne; rcases i with _ | _ | i
    · decide
    · exact absurd rfl hne
    · omega

/-- The concrete address map `i ↦ ⟨i + 1⟩` is injective on `{0, 1}`. -/
theorem a₀_inj : ∀ i l, i < 2 → l < 2 →
    (fun i : Nat => (⟨i + 1⟩ : Ref)) i = (fun i : Nat => (⟨i + 1⟩ : Ref)) l → i = l := by
  intro i l _ _ he
  have h := congrArg Ref.addr he
  simp at h
  omega

/-- The concrete addresses are non-NULL. -/
theorem a₀_nn : ∀ i, i < 2 → (fun i : Nat => (⟨i + 1⟩ : Ref)) i ≠ Ref.null := by
  intro i _ h
  simp at h

/-- **End-to-end bug witness.**  From a state satisfying the precondition
    (`y = 3` already in the list `1 → 3`), running the buggy insert actually
    reaches a state with two reachable nodes carrying key `3`: the scan walks
    past the `3`, the duplicate check sees NULL, and a second `3` is appended. -/
theorem insert_bug_witness :
    ∃ t s, Pre 2 (fun i => ⟨i + 1⟩) (fun i => 2 * i + 1) 3 s ∧
      (insertProg, s) ⟹ t ∧ hasDupKey 3 t := by
  have htri := insert_triple (m := 2) (p := 2) (yv := 3) (a := fun i => ⟨i + 1⟩)
    (k₀ := fun i => 2 * i + 1) (r := ⟨3⟩)
    (by decide) (by decide) (by decide)
    (by
      intro i hi
      omega)
    (by
      intro h
      omega)
    a₀_inj a₀_nn
  obtain ⟨s, hs, hrun⟩ := htri t₀ t₀_post
  exact ⟨t₀, s, hs, hrun,
    post_dup (j := 1) (by decide) (by decide) (by decide) (by decide) t₀ t₀_post⟩

/-- The same witness phrased through the packaged triple and the advisor's
    two informal predicates. -/
theorem insert_bug_witness_any :
    ∃ t s, PreAny 3 s ∧ hasKey 3 s ∧ (insertProg, s) ⟹ t ∧ hasDupKey 3 t := by
  obtain ⟨t, s, hs, hrun, hdup⟩ := insert_bug_witness
  have hpre : PreAny 3 s :=
    ⟨2, fun i => ⟨i + 1⟩, fun i => 2 * i + 1, by decide, a₀_inj, a₀_nn,
     ⟨1, by decide, by decide⟩, hs⟩
  exact ⟨t, s, hpre, preAny_hasKey hpre, hrun, hdup⟩

-- ------------------------------------------------------------
-- Non-emptiness of the front case (unsorted list 5 → 3, insert 3)
-- ------------------------------------------------------------

/-- Concrete front-insertion state: the unsorted list `5 → 3` (nodes ⟨1⟩,
    ⟨2⟩) with the fresh node ⟨3⟩ (key 3) as the new head: `3 → 5 → 3`. -/
def t₁ : State :=
  { vars := fun τ x =>
      match τ with
      | .ref => if x = "head" then ⟨3⟩ else if x = "curr" then ⟨1⟩
                else if x = "prev" then Ref.null else if x = "n" then ⟨3⟩ else Ref.null
      | .nat => if x = "y" then 3 else 0
      | .map .ref .nat => fun q => if q = ⟨1⟩ then 5 else if q = ⟨2⟩ then 3
                                   else if q = ⟨3⟩ then 3 else 0
      | .map .ref .ref => fun q => if q = ⟨1⟩ then ⟨2⟩ else if q = ⟨3⟩ then ⟨1⟩ else Ref.null
      | τ => τ.default
    alloc := fun q => decide (1 ≤ q.addr ∧ q.addr ≤ 3) }

theorem t₁_post :
    PostFront 2 (fun i => ⟨i + 1⟩) (fun i => if i = 0 then 5 else 3) 3 ⟨3⟩ t₁ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro i hi; rcases i with _ | _ | i
    · decide
    · decide
    · omega
  · decide
  · intro i hi; rcases i with _ | _ | i
    · decide
    · decide
    · omega
  · decide
  · decide
  · intro i hi; rcases i with _ | _ | i
    · decide
    · decide
    · omega
  · intro i hi; rcases i with _ | _ | i
    · decide
    · decide
    · omega

/-- **Front-case witness.**  From the unsorted list `5 → 3` with `y = 3`, the
    scan stops at the head (`5 > 3`), the check sees key `5 ≠ 3`, and the new
    node becomes the head: `3 → 5 → 3` has two reachable nodes with key `3`.
    (As explained in the header, this duplicate is due to the unsorted input,
    not to the `≤` bug.) -/
theorem insert_front_witness :
    ∃ t s, Pre 2 (fun i => ⟨i + 1⟩) (fun i => if i = 0 then 5 else 3) 3 s ∧
      (insertProg, s) ⟹ t ∧ hasDupKey 3 t := by
  have htri := insert_triple_front (m := 2) (yv := 3) (a := fun i => ⟨i + 1⟩)
    (k₀ := fun i => if i = 0 then 5 else 3) (r := ⟨3⟩) (by decide) (by decide) a₀_nn
  obtain ⟨s, hs, hrun⟩ := htri t₁ t₁_post
  exact ⟨t₁, s, hs, hrun, post_dup_front (j := 1) (by decide) (by decide) t₁ t₁_post⟩

end MapLang.LinkedList
