import Lean

/-!
# MapLang — the core language with first-class maps

This module is the language extension requested by the advisor: **maps,
sets and relations become values that program variables can hold**, and a
distinct pointer type `Ref` (the *Node* identity) is added.  Everything is
self-contained (no import from the old `Language`), so all existing proofs
remain untouched.

## Design in one paragraph

* `Ref` — the address / node-identity type.  It is a *new* nominal type:
  mixing a `Ref` with a `Nat` is a type error (`⟨0⟩` plays the role of
  `NULL`).
* `Ty` — the small type universe of program values:
  `nat | bool | ref | map dom cod`.  Combinations are built with `map`:
  `map ref nat` is the advisor's `key : Node → Nat`, `map ref ref` is
  `next : Node → Node`, `map nat nat` is an array, `map ref bool` is a set
  of nodes, `map ref (map ref bool)` is a binary relation on nodes.
  A new map / set / relation therefore needs **no change to the language**
  — the user just declares a variable of the wanted `Ty`.
* `Ty.denote` — the Lean type each `Ty` stands for (`map a b` becomes the
  Lean function type `a.denote → b.denote`).  So the *value* of the `key`
  variable really is a function `Ref → Nat`: this is the "two arrays"
  picture, `key` holding the data and `next` holding the addresses.
* `Var τ` — a program variable **tagged with its type**.  `curr : Var .ref`
  can only ever be read / written as a `Ref` (the advisor's "curr and prev
  are variables of type Node only").
* `State` — a *typed store*: for every type `τ` and every name a value of
  `τ.denote`, plus the allocation record `alloc : Ref → Bool` (which nodes
  exist).  Reading is `s⟦x⟧`, writing is `s[x ↦ v]`.
* `Stmt` / `BigStep` — the old statements, plus the new ones:
  `assign x e` (typed, any `Ty`), `mapUpdate m k v` (`m[k] := v`, the
  McCarthy store on a map-valued variable), `alloc x` (`x := new`), the
  set operations `setInsert S e` / `setRemove S e` and the relation
  operations `relInsert R x y` / `relRemove R x y`.  Set-valued expressions
  (`∅`, `∪`, `∩`, `\`, membership, subset) are in the `SetV` namespace,
  relation-valued ones (`∅`, membership, `∪`, `∩`, converse, composition,
  subset) in the `RelV` namespace; both are used inside `assign`, exactly as
  map reads are.
-/

namespace MapLang

-- ============================================================
-- §1  Ref — the address / node-identity type
-- ============================================================

/-- Address (pointer) type.  Nominally distinct from `Nat`: `Ref` and `Nat`
    values cannot be mixed.  This is the language-level *Node* type. -/
structure Ref where
  addr : Nat
deriving DecidableEq, Repr

/-- The NULL pointer. -/
def Ref.null : Ref := ⟨0⟩

instance : Inhabited Ref := ⟨Ref.null⟩

@[simp] theorem Ref.null_addr : Ref.null.addr = 0 := rfl
@[simp] theorem Ref.mk_eq_null {n : Nat} : (Ref.mk n = Ref.null) ↔ n = 0 := by
  constructor
  · intro h; exact congrArg Ref.addr h
  · intro h; subst h; rfl
@[simp] theorem Ref.null_eq_mk {n : Nat} : (Ref.null = Ref.mk n) ↔ n = 0 := by
  rw [eq_comm]; exact Ref.mk_eq_null

/-- Normal form for equations on addresses: `r.addr = n` becomes `r = ⟨n⟩`, so
    that an existential over a `Ref` can be eliminated by `exists_eq_left`. -/
@[simp] theorem Ref.addr_eq_iff {r : Ref} {n : Nat} : (r.addr = n) ↔ r = Ref.mk n := by
  constructor
  · intro h; cases r; cases h; rfl
  · intro h; subst h; rfl
@[simp] theorem Ref.eq_addr_iff {r : Ref} {n : Nat} : (n = r.addr) ↔ r = Ref.mk n := by
  rw [eq_comm]; exact Ref.addr_eq_iff

-- ============================================================
-- §2  Ty — the type universe of program values
-- ============================================================

/-- Types of program values.  `map dom cod` is the type of (total) maps from
    `dom` to `cod`; sets and relations are maps into `bool`. -/
inductive Ty where
  | nat
  | bool
  | ref
  | map (dom cod : Ty)
deriving DecidableEq, Repr

/-- `a ⇒ b` is the map type from `a` to `b`. -/
scoped infixr:25 " ⇒ " => Ty.map

/-- A set of `a`-values is a map `a ⇒ bool`. -/
abbrev Ty.set (a : Ty) : Ty := .map a .bool

/-- A binary relation between `a`- and `b`-values is a map `a ⇒ b ⇒ bool`. -/
abbrev Ty.rel (a b : Ty) : Ty := .map a (.map b .bool)

/-- The Lean type denoted by a program type.  Maps denote Lean functions. -/
abbrev Ty.denote : Ty → Type
  | .nat     => Nat
  | .bool    => Bool
  | .ref     => Ref
  | .map a b => a.denote → b.denote

/-- Every program type has a default (zero / false / NULL / constant) value. -/
def Ty.default : (τ : Ty) → τ.denote
  | .nat     => 0
  | .bool    => false
  | .ref     => Ref.null
  | .map _ b => fun _ => b.default

instance (τ : Ty) : Inhabited τ.denote := ⟨τ.default⟩

-- The base types have decidable equality (needed to write `m[k] := v`).
instance : DecidableEq (Ty.denote .nat)  := inferInstanceAs (DecidableEq Nat)
instance : DecidableEq (Ty.denote .bool) := inferInstanceAs (DecidableEq Bool)
instance : DecidableEq (Ty.denote .ref)  := inferInstanceAs (DecidableEq Ref)

-- ------------------------------------------------------------
-- §2.1  Set-valued expressions
-- ------------------------------------------------------------

/-!
A set of `a`-values is represented by its membership map `a.denote → Bool`
(the program type `Ty.set a = map a bool`).  The operations below are the
expression-level set operations; they are ordinary Lean functions, so their
meaning is their definition, and they are used inside `Stmt.assign` exactly
as map reads are.  Each comes with a `@[simp]` unfolding lemma, so the
automation unfolds it.
-/
namespace SetV
variable {a : Ty}

/-- `∅` -/
def empty : (Ty.set a).denote := fun _ => false
/-- `x ∈ A` -/
@[simp] def mem (x : a.denote) (A : (Ty.set a).denote) : Prop := A x = true
/-- `A ∪ B` -/
def union (A B : (Ty.set a).denote) : (Ty.set a).denote := fun y => A y || B y
/-- `A ∩ B` -/
def inter (A B : (Ty.set a).denote) : (Ty.set a).denote := fun y => A y && B y
/-- `A \ B` -/
def diff (A B : (Ty.set a).denote) : (Ty.set a).denote := fun y => A y && !B y
/-- `A ∪ {x}` -/
def insert [DecidableEq a.denote] (x : a.denote) (A : (Ty.set a).denote) :
    (Ty.set a).denote := fun y => if y = x then true else A y
/-- `A \ {x}` -/
def erase [DecidableEq a.denote] (x : a.denote) (A : (Ty.set a).denote) :
    (Ty.set a).denote := fun y => if y = x then false else A y
/-- `A ⊆ B` -/
@[simp] def subset (A B : (Ty.set a).denote) : Prop := ∀ y, A y = true → B y = true

-- Unfolding lemmas in UNAPPLIED form.  (The equation lemmas Lean generates
-- for a function-valued `def` are eta-expanded, so they only fire on
-- `inter A B y`; a goal `C = inter A B` needs these.)
@[simp] theorem empty_def : (empty : (Ty.set a).denote) = fun _ => false := rfl
@[simp] theorem union_def (A B : (Ty.set a).denote) :
    union A B = fun y => A y || B y := rfl
@[simp] theorem inter_def (A B : (Ty.set a).denote) :
    inter A B = fun y => A y && B y := rfl
@[simp] theorem diff_def (A B : (Ty.set a).denote) :
    diff A B = fun y => A y && !B y := rfl
@[simp] theorem insert_def [DecidableEq a.denote] (x : a.denote) (A : (Ty.set a).denote) :
    insert x A = fun y => if y = x then true else A y := rfl
@[simp] theorem erase_def [DecidableEq a.denote] (x : a.denote) (A : (Ty.set a).denote) :
    erase x A = fun y => if y = x then false else A y := rfl

end SetV

-- ------------------------------------------------------------
-- §2.2  Relation-valued expressions
-- ------------------------------------------------------------

/-!
A binary relation between `a`- and `b`-values is represented by its
characteristic map `a.denote → b.denote → Bool` (the program type
`Ty.rel a b = map a (map b bool)`): `R x y = true` means `(x, y) ∈ R`.  As
for sets, the operations below are ordinary Lean functions, used inside
`Stmt.assign`, each with an unapplied `@[simp]` unfolding lemma.

Composition quantifies over the middle element, whose type may be infinite
(`nat`), so its Boolean value is chosen classically.  This costs nothing
here: MapLang is a shallow embedding, expressions are Lean functions of the
state that are reasoned about, never executed.
-/
namespace RelV
variable {a b c : Ty}

/-- `∅` -/
def empty : (Ty.rel a b).denote := fun _ _ => false
/-- `(x, y) ∈ R` -/
@[simp] def mem (x : a.denote) (y : b.denote) (R : (Ty.rel a b).denote) : Prop := R x y = true
/-- `R ∪ S` -/
def union (R S : (Ty.rel a b).denote) : (Ty.rel a b).denote := fun x y => R x y || S x y
/-- `R ∩ S` -/
def inter (R S : (Ty.rel a b).denote) : (Ty.rel a b).denote := fun x y => R x y && S x y
/-- `R⁻¹` (converse): `(y, x) ∈ R⁻¹ ↔ (x, y) ∈ R`. -/
def inv (R : (Ty.rel a b).denote) : (Ty.rel b a).denote := fun y x => R x y
/-- `R ⨾ S` (relational composition, first `R` then `S`):
    `(x, z) ∈ R ⨾ S ↔ ∃ y, (x, y) ∈ R ∧ (y, z) ∈ S`. -/
noncomputable def comp (R : (Ty.rel a b).denote) (S : (Ty.rel b c).denote) :
    (Ty.rel a c).denote :=
  fun x z => @decide (∃ y, R x y = true ∧ S y z = true) (Classical.propDecidable _)
/-- `R ∪ {(x, y)}` -/
def insert [DecidableEq a.denote] [DecidableEq b.denote] (x : a.denote) (y : b.denote)
    (R : (Ty.rel a b).denote) : (Ty.rel a b).denote :=
  fun x' y' => if x' = x ∧ y' = y then true else R x' y'
/-- `R \ {(x, y)}` -/
def erase [DecidableEq a.denote] [DecidableEq b.denote] (x : a.denote) (y : b.denote)
    (R : (Ty.rel a b).denote) : (Ty.rel a b).denote :=
  fun x' y' => if x' = x ∧ y' = y then false else R x' y'
/-- `R ⊆ S` -/
@[simp] def subset (R S : (Ty.rel a b).denote) : Prop := ∀ x y, R x y = true → S x y = true

-- Unfolding lemmas in UNAPPLIED form (see the remark in `SetV`).
@[simp] theorem empty_def : (empty : (Ty.rel a b).denote) = fun _ _ => false := rfl
@[simp] theorem union_def (R S : (Ty.rel a b).denote) :
    union R S = fun x y => R x y || S x y := rfl
@[simp] theorem inter_def (R S : (Ty.rel a b).denote) :
    inter R S = fun x y => R x y && S x y := rfl
@[simp] theorem inv_def (R : (Ty.rel a b).denote) : inv R = fun y x => R x y := rfl
@[simp] theorem comp_def (R : (Ty.rel a b).denote) (S : (Ty.rel b c).denote) :
    comp R S = fun x z => @decide (∃ y, R x y = true ∧ S y z = true) (Classical.propDecidable _) :=
  rfl
@[simp] theorem insert_def [DecidableEq a.denote] [DecidableEq b.denote] (x : a.denote)
    (y : b.denote) (R : (Ty.rel a b).denote) :
    insert x y R = fun x' y' => if x' = x ∧ y' = y then true else R x' y' := rfl
@[simp] theorem erase_def [DecidableEq a.denote] [DecidableEq b.denote] (x : a.denote)
    (y : b.denote) (R : (Ty.rel a b).denote) :
    erase x y R = fun x' y' => if x' = x ∧ y' = y then false else R x' y' := rfl

/-- Membership in a composition, in `Prop` form. -/
theorem mem_comp {R : (Ty.rel a b).denote} {S : (Ty.rel b c).denote} {x : a.denote}
    {z : c.denote} : comp R S x z = true ↔ ∃ y, R x y = true ∧ S y z = true := by
  simp

/-- Membership in the converse. -/
theorem mem_inv {R : (Ty.rel a b).denote} {x : a.denote} {y : b.denote} :
    inv R y x = R x y := rfl

end RelV

-- ============================================================
-- §3  Var — typed program variables
-- ============================================================

/-- A program variable carrying its type.  Two variables are the same slot of
    the store iff they have the same type *and* the same name. -/
structure Var (τ : Ty) where
  name : String
deriving DecidableEq, Repr

open Lean Meta in
/-- If `e` is `c.name` for a global constant `c` declared as
    `def c : Var τ := ⟨"…"⟩`, return that string. -/
private def varNameLit? (e : Expr) : MetaM (Option String) := do
  let_expr Var.name _ v := e | return none
  let .const c _ := v.getAppFn | return none
  let some info := (← getEnv).find? c | return none
  let some val := info.value? | return none
  let val ← whnfR val
  let_expr Var.mk _ str := val | return none
  match str with
  | .lit (.strVal s) => return some s
  | _ => return none

open Lean Meta Simp in
/-- Simp-procedure: decide `c₁.name = c₂.name` for global constants `c₁ c₂`
    declared as `def c : Var τ := ⟨"…"⟩`.  This lets plain `simp` discharge
    the side conditions `y ≠ x.name` of the read-after-write lemmas without a
    global `decide := true`, while leaving the terms `c.name` themselves
    untouched (so that name-keyed simp lemmas keep matching). -/
simproc ↓ decideVarNameEq (Var.name _ = Var.name _) := fun e => do
  let_expr Eq _ l r := e | return .continue
  let some sl ← varNameLit? l | return .continue
  let some sr ← varNameLit? r | return .continue
  if sl == sr then
    return .done { expr := mkConst ``True, proof? := ← mkEqTrue (← mkDecideProof e) }
  else
    return .done { expr := mkConst ``False, proof? := ← mkEqFalse (← mkDecideProof (mkNot e)) }

-- ============================================================
-- §4  State — the typed store + allocation record
-- ============================================================

/-- Program state.
    * `vars τ x` : the value of the variable named `x` at type `τ`
    * `alloc r`  : whether the node `r` has been allocated (`new`) -/
structure State where
  vars  : (τ : Ty) → String → τ.denote
  alloc : Ref → Bool

/-- Read a typed variable: `s⟦x⟧`.  Marked `@[simp]` so that every read is
    normalised to the primitive `s.vars τ x.name` form inside proofs (one
    canonical atom for `omega`); the unexpander below prints that primitive
    form back as `s⟦x⟧`. -/
@[simp] abbrev State.get (s : State) {τ : Ty} (x : Var τ) : τ.denote := s.vars τ x.name

scoped notation:max s "⟦" x "⟧" => State.get s x

open Lean PrettyPrinter in
/-- Print `s.vars τ x.name` as `s⟦x⟧`. -/
@[app_unexpander State.vars] def unexpandStateVars : Unexpander
  | `($_ $s $_ (Var.name $x))         => `($s⟦$x⟧)
  | `($_ $s $_ ($x).name)             => `($s⟦$x⟧)
  | `($_ $s $_ (Var.name $x) $args*)  => `($s⟦$x⟧ $args*)
  | `($_ $s $_ ($x).name $args*)      => `($s⟦$x⟧ $args*)
  | _ => throw ()

/-- Write a typed variable: `s[x ↦ v]`.  Only the slot `(τ, x.name)` changes. -/
def State.update (s : State) {τ : Ty} (x : Var τ) (v : τ.denote) : State :=
  { s with vars := fun τ' y =>
      if h : τ' = τ then (if y = x.name then h ▸ v else s.vars τ' y)
      else s.vars τ' y }

scoped notation:max s "[" x " ↦ " v "]" => State.update s x v

/-- Map write `m[k] := v`: the McCarthy store on the map-valued variable `m`. -/
def State.mapUpd (s : State) {a b : Ty} [DecidableEq a.denote] (m : Var (.map a b))
    (k : a.denote) (v : b.denote) : State :=
  s[m ↦ fun i => if i = k then v else s⟦m⟧ i]

/-- Set insertion `S := S ∪ {k}`: the membership map of `S` answers `true` at `k`.
    It is the map write `S[k] := true`; `@[simp]` normalises it to `mapUpd`
    so that every read-after-write lemma applies. -/
@[simp] def State.setIns (s : State) {a : Ty} [DecidableEq a.denote]
    (S : Var (.map a .bool)) (k : a.denote) : State :=
  s.mapUpd S k true

/-- Set removal `S := S \ {k}`: the map write `S[k] := false`. -/
@[simp] def State.setRem (s : State) {a : Ty} [DecidableEq a.denote]
    (S : Var (.map a .bool)) (k : a.denote) : State :=
  s.mapUpd S k false

/-- Relation point write `R[i][j] := w`: the pair `(i, j)` gets membership bit
    `w`, every other pair keeps its bit.  (A dedicated operation, not the
    nested map write `R[i] := …`, so that its elimination lemma needs only the
    old *bit* at `(i, j)` and never the old *row* `R i`, a function.) -/
def State.relUpd (s : State) {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
    (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote) (w : Bool) : State :=
  s[R ↦ fun k l => if k = i ∧ l = j then w else s⟦R⟧ k l]

/-- Relation insertion `R := R ∪ {(i, j)}`. -/
@[simp] def State.relIns (s : State) {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
    (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote) : State :=
  s.relUpd R i j true

/-- Relation removal `R := R \ {(i, j)}`. -/
@[simp] def State.relRem (s : State) {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
    (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote) : State :=
  s.relUpd R i j false

/-- Allocation `x := new`: bind `x` to the (fresh) node `r` and mark `r` allocated. -/
def State.doAlloc (s : State) (x : Var .ref) (r : Ref) : State :=
  { vars  := (s[x ↦ r]).vars
    alloc := fun q => if q = r then true else s.alloc q }

/-- Two states are equal if every slot and the allocation record agree. -/
theorem State.ext' {s t : State}
    (h1 : ∀ τ x, s.vars τ x = t.vars τ x) (h2 : ∀ r, s.alloc r = t.alloc r) : s = t := by
  cases s; cases t
  have e1 : _ = _ := funext fun τ => funext fun x => h1 τ x
  have e2 := funext h2
  simp only at e1 e2
  subst e1; subst e2; rfl

-- ------------------------------------------------------------
-- §4.1  Read-after-write lemmas (the automation's simp set)
-- ------------------------------------------------------------

@[simp] theorem State.update_same (s : State) {τ : Ty} (x : Var τ) (v : τ.denote) :
    (s[x ↦ v]).vars τ x.name = v := by
  simp [State.update]

@[simp] theorem State.update_ne_ty (s : State) {τ τ' : Ty} (x : Var τ) (y : String)
    (v : τ.denote) (h : τ' ≠ τ) : (s[x ↦ v]).vars τ' y = s.vars τ' y := by
  unfold State.update; simp only; split <;> simp_all

@[simp] theorem State.update_ne_name (s : State) {τ τ' : Ty} (x : Var τ) (y : String)
    (v : τ.denote) (h : y ≠ x.name) : (s[x ↦ v]).vars τ' y = s.vars τ' y := by
  unfold State.update; simp only; split <;> simp_all

@[simp] theorem State.update_alloc (s : State) {τ : Ty} (x : Var τ) (v : τ.denote) :
    (s[x ↦ v]).alloc = s.alloc := rfl

/-- Reading a written map at any index: `(m[k] := v)[i] = if i = k then v else m[i]`. -/
@[simp] theorem State.mapUpd_same (s : State) {a b : Ty} [DecidableEq a.denote]
    (m : Var (.map a b)) (k : a.denote) (v : b.denote) :
    (s.mapUpd m k v).vars (.map a b) m.name = fun i => if i = k then v else s⟦m⟧ i := by
  unfold State.mapUpd; exact State.update_same _ _ _

@[simp] theorem State.mapUpd_ne_ty (s : State) {a b τ' : Ty} [DecidableEq a.denote]
    (m : Var (.map a b)) (k : a.denote) (v : b.denote) (y : String) (h : τ' ≠ .map a b) :
    (s.mapUpd m k v).vars τ' y = s.vars τ' y := by
  unfold State.mapUpd; exact State.update_ne_ty _ _ _ _ h

@[simp] theorem State.mapUpd_ne_name (s : State) {a b τ' : Ty} [DecidableEq a.denote]
    (m : Var (.map a b)) (k : a.denote) (v : b.denote) (y : String) (h : y ≠ m.name) :
    (s.mapUpd m k v).vars τ' y = s.vars τ' y := by
  unfold State.mapUpd; exact State.update_ne_name _ _ _ _ h

@[simp] theorem State.mapUpd_alloc (s : State) {a b : Ty} [DecidableEq a.denote]
    (m : Var (.map a b)) (k : a.denote) (v : b.denote) :
    (s.mapUpd m k v).alloc = s.alloc := rfl

/-- Reading a written relation at any pair. -/
@[simp] theorem State.relUpd_same (s : State) {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote)
    (w : Bool) :
    (s.relUpd R i j w).vars (.map a (.map b .bool)) R.name
      = fun k l => if k = i ∧ l = j then w else s⟦R⟧ k l := by
  unfold State.relUpd; exact State.update_same _ _ _

@[simp] theorem State.relUpd_ne_ty (s : State) {a b τ' : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote)
    (w : Bool) (y : String) (h : τ' ≠ .map a (.map b .bool)) :
    (s.relUpd R i j w).vars τ' y = s.vars τ' y := by
  unfold State.relUpd; exact State.update_ne_ty _ _ _ _ h

@[simp] theorem State.relUpd_ne_name (s : State) {a b τ' : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote)
    (w : Bool) (y : String) (h : y ≠ R.name) :
    (s.relUpd R i j w).vars τ' y = s.vars τ' y := by
  unfold State.relUpd; exact State.update_ne_name _ _ _ _ h

@[simp] theorem State.relUpd_alloc (s : State) {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote)
    (w : Bool) : (s.relUpd R i j w).alloc = s.alloc := rfl

@[simp] theorem State.doAlloc_vars (s : State) (x : Var .ref) (r : Ref) :
    (s.doAlloc x r).vars = (s[x ↦ r]).vars := rfl

@[simp] theorem State.doAlloc_alloc (s : State) (x : Var .ref) (r : Ref) (q : Ref) :
    (s.doAlloc x r).alloc q = if q = r then true else s.alloc q := rfl

-- ------------------------------------------------------------
-- §4.2  Overwrite / identity lemmas (for the elimination proofs)
-- ------------------------------------------------------------

theorem State.update_update (s : State) {τ : Ty} (x : Var τ) (v w : τ.denote) :
    (s[x ↦ v])[x ↦ w] = s[x ↦ w] := by
  refine State.ext' (fun τ' y => ?_) (fun _ => rfl)
  by_cases hτ : τ' = τ
  · subst hτ
    by_cases hy : y = x.name
    · subst hy; simp
    · simp [hy]
  · simp [hτ]

theorem State.update_self (s : State) {τ : Ty} (x : Var τ) : s[x ↦ s⟦x⟧] = s := by
  refine State.ext' (fun τ' y => ?_) (fun _ => rfl)
  by_cases hτ : τ' = τ
  · subst hτ
    by_cases hy : y = x.name
    · subst hy; simp
    · simp [hy]
  · simp [hτ]

theorem State.update_eq_self (s : State) {τ : Ty} (x : Var τ) (v : τ.denote)
    (h : s⟦x⟧ = v) : s[x ↦ v] = s := by
  rw [← h]; exact State.update_self s x

/-- Writes to two *different* slots commute. -/
theorem State.update_comm (s : State) {τ τ' : Ty} (x : Var τ) (x' : Var τ')
    (v : τ.denote) (w : τ'.denote) (h : τ ≠ τ' ∨ x.name ≠ x'.name) :
    (s[x ↦ v])[x' ↦ w] = (s[x' ↦ w])[x ↦ v] := by
  refine State.ext' (fun σ z => ?_) (fun _ => rfl)
  by_cases hσ : σ = τ
  · subst hσ
    by_cases hz : z = x.name
    · subst hz
      rcases h with h | h
      · simp [h]
      · simp [h]
    · by_cases hσ' : σ = τ'
      · subst hσ'
        by_cases hz' : z = x'.name
        · subst hz'; simp [hz]
        · simp [hz, hz']
      · simp [hz, hσ']
  · by_cases hσ' : σ = τ'
    · subst hσ'
      by_cases hz' : z = x'.name
      · subst hz'; simp [hσ]
      · simp [hσ, hz']
    · simp [hσ, hσ']

theorem State.mapUpd_mapUpd (s : State) {a b : Ty} [DecidableEq a.denote]
    (m : Var (.map a b)) (k : a.denote) (v w : b.denote) :
    (s.mapUpd m k v).mapUpd m k w = s.mapUpd m k w := by
  unfold State.mapUpd
  rw [State.update_update]
  congr 1
  funext i
  by_cases hi : i = k
  · simp [hi]
  · simp [hi]

theorem State.mapUpd_self (s : State) {a b : Ty} [DecidableEq a.denote]
    (m : Var (.map a b)) (k : a.denote) : s.mapUpd m k (s⟦m⟧ k) = s := by
  unfold State.mapUpd
  have : (fun i => if i = k then s⟦m⟧ k else s⟦m⟧ i) = s⟦m⟧ := by
    funext i; by_cases hi : i = k
    · subst hi; simp
    · simp [hi]
  rw [this]; exact State.update_self s m

theorem State.relUpd_relUpd (s : State) {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote)
    (v w : Bool) : (s.relUpd R i j v).relUpd R i j w = s.relUpd R i j w := by
  unfold State.relUpd
  rw [State.update_update]
  congr 1
  funext k l
  by_cases h : k = i ∧ l = j
  · simp only [h, and_self, ↓reduceIte]
  · simp only [h, ↓reduceIte, State.get, State.update_same]

theorem State.relUpd_self (s : State) {a b : Ty} [DecidableEq a.denote]
    [DecidableEq b.denote] (R : Var (.map a (.map b .bool))) (i : a.denote) (j : b.denote) :
    s.relUpd R i j (s⟦R⟧ i j) = s := by
  unfold State.relUpd
  have : (fun k l => if k = i ∧ l = j then s⟦R⟧ i j else s⟦R⟧ k l) = s⟦R⟧ := by
    funext k l
    by_cases h : k = i ∧ l = j
    · obtain ⟨rfl, rfl⟩ := h; simp
    · simp only [h, ↓reduceIte]
  rw [this]; exact State.update_self s R

-- ============================================================
-- §5  Stmt — abstract syntax
-- ============================================================

/-- Statements.  Expressions are shallow (functions of the state), exactly as
    in the old language.  New constructors:
    * `assign x e`      — `x := e`, for a variable of *any* type (incl. maps)
    * `mapUpdate m k v` — `m[k] := v`, point-update of a map-valued variable
    * `alloc x`         — `x := new`, a fresh (unallocated, non-NULL) node
    * `setInsert S e`   — `S := S ∪ {e}` on a set-valued variable
    * `setRemove S e`   — `S := S \ {e}` on a set-valued variable
    * `relInsert R x y` — `R := R ∪ {(x, y)}` on a relation-valued variable
    * `relRemove R x y` — `R := R \ {(x, y)}` on a relation-valued variable -/
inductive Stmt : Type where
  | skip       : Stmt
  | assign     {τ : Ty} (x : Var τ) (e : State → τ.denote) : Stmt
  | mapUpdate  {a b : Ty} [DecidableEq a.denote] (m : Var (.map a b))
               (k : State → a.denote) (v : State → b.denote) : Stmt
  | alloc      (x : Var .ref) : Stmt
  | setInsert  {a : Ty} [DecidableEq a.denote] (S : Var (.map a .bool))
               (k : State → a.denote) : Stmt
  | setRemove  {a : Ty} [DecidableEq a.denote] (S : Var (.map a .bool))
               (k : State → a.denote) : Stmt
  | relInsert  {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
               (R : Var (.map a (.map b .bool))) (x : State → a.denote) (y : State → b.denote) :
               Stmt
  | relRemove  {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
               (R : Var (.map a (.map b .bool))) (x : State → a.denote) (y : State → b.denote) :
               Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt
  | assert     : (State → Prop) → Stmt
  | assume     : (State → Prop) → Stmt

scoped infixr:90 "; " => Stmt.seq

-- ============================================================
-- §6  Big-step operational semantics
-- ============================================================

/-- `(S, s) ⟹ t` : executing `S` from state `s` terminates in state `t`. -/
inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
      BigStep (Stmt.skip, s) s
  | assign {τ : Ty} (x : Var τ) (e : State → τ.denote) (s) :
      BigStep (Stmt.assign x e, s) (s[x ↦ e s])
  | mapUpdate {a b : Ty} [DecidableEq a.denote] (m : Var (.map a b))
      (k : State → a.denote) (v : State → b.denote) (s) :
      BigStep (Stmt.mapUpdate m k v, s) (s.mapUpd m (k s) (v s))
  | alloc (x : Var .ref) (r : Ref) (s)
      (hfresh : s.alloc r = false) (hnn : r ≠ Ref.null) :
      BigStep (Stmt.alloc x, s) (s.doAlloc x r)
  | setInsert {a : Ty} [DecidableEq a.denote] (S : Var (.map a .bool))
      (k : State → a.denote) (s) :
      BigStep (Stmt.setInsert S k, s) (s.setIns S (k s))
  | setRemove {a : Ty} [DecidableEq a.denote] (S : Var (.map a .bool))
      (k : State → a.denote) (s) :
      BigStep (Stmt.setRemove S k, s) (s.setRem S (k s))
  | relInsert {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
      (R : Var (.map a (.map b .bool))) (x : State → a.denote) (y : State → b.denote) (s) :
      BigStep (Stmt.relInsert R x y, s) (s.relIns R (x s) (y s))
  | relRemove {a b : Ty} [DecidableEq a.denote] [DecidableEq b.denote]
      (R : Var (.map a (.map b .bool))) (x : State → a.denote) (y : State → b.denote) (s) :
      BigStep (Stmt.relRemove R x y, s) (s.relRem R (x s) (y s))
  | seq (S T s t u)
      (hS : BigStep (S, s) t)
      (hT : BigStep (T, t) u) :
      BigStep (S; T, s) u
  | if_true (B S T s t)
      (hcond : B s)
      (hbody : BigStep (S, s) t) :
      BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t)
      (hcond : ¬ B s)
      (hbody : BigStep (T, s) t) :
      BigStep (Stmt.ifThenElse B S T, s) t
  | while_true (B S s t u)
      (hcond : B s)
      (hbody : BigStep (S, s) t)
      (hrest : BigStep (Stmt.whileDo B S, t) u) :
      BigStep (Stmt.whileDo B S, s) u
  | while_false (B S s)
      (hcond : ¬ B s) :
      BigStep (Stmt.whileDo B S, s) s
  | assert_ok (B s)
      (hcond : B s) :
      BigStep (Stmt.assert B, s) s
  | assert_er (B s)
      (hcond : ¬ B s) :
      BigStep (Stmt.assert B, s) s
  | assume (B s)
      (hcond : B s) :
      BigStep (Stmt.assume B, s) s

scoped infix:110 " ⟹ " => BigStep

/-- Replace the result state by an equal one (handy when building derivations). -/
theorem BigStep.cast {c : Stmt} {s t t' : State}
    (h : (c, s) ⟹ t) (e : t = t') : (c, s) ⟹ t' := e ▸ h

end MapLang
