import Lean

namespace Language
-- 1. State Definition
-- States map variable names (Strings) to values (Natural Numbers).
def State := String → Nat -- Val

-- State update function: s[name ↦ val]
def State.update (name : String) (val : Nat) (s : State) : State :=
  fun x => if x = name then val else s x

-- Notation for state update
notation s "[" x " ↦ " v "]" => State.update x v s

-- 2. Statements - Abstract Syntax Tree
inductive Stmt : Type where
  | skip       : Stmt
  | assign     : String → (State → Nat) → Stmt
  | seq        : Stmt → Stmt → Stmt
  | ifThenElse : (State → Prop) → Stmt → Stmt → Stmt
  | whileDo    : (State → Prop) → Stmt → Stmt
  | assert : (State → Prop) → Stmt
  | assume : (State → Prop) → Stmt

infixr:90 "; " => Stmt.seq

-- 3. Big-Step Semantics (Operational Semantics)
-- (S, s) ⟹ t means "Execution of S starting in state s terminates in state t"
inductive BigStep : Stmt × State → State → Prop where
  | skip (s) :
      BigStep (Stmt.skip, s) s
  | assign (x a s) :
      BigStep (Stmt.assign x a, s) (s[x ↦ a s])
      -- x = y + 1
      -- Stmt.assign x (y + 1)
  | seq (S T s t u)
        (hS : BigStep (S, s) t)
        (hT : BigStep (T, t) u) :
      BigStep (S; T, s) u
  -- if B then S else T
  | if_true (B S T s t)
        (hcond : B s)
        (hbody : BigStep (S, s) t) :
      BigStep (Stmt.ifThenElse B S T, s) t
  | if_false (B S T s t)
        (hcond : ¬ B s)
        (hbody : BigStep (T, s) t) :
      BigStep (Stmt.ifThenElse B S T, s) t
  -- while B do S
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

-- Notation for BigStep semantics
infix:110 " ⟹ " => BigStep

end Language
