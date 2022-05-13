inductive Binary where
  | add | sub | mul | div | mod

inductive Unary where
  | neg | abs | signum

inductive Expr where
  | var (name : String)
  | lit (val : Int)
  | binop (lhs : Expr) (op : Binary) (rhs : Expr)
  | unop (op : Unary) (rhs : Expr)

inductive Comparison where
  | eq | neq | leq | geq | lt | gt

inductive Connective where
  | land | lor | lxor

inductive Cond where
  | lit (val : Bool)
  | comp (lhs : Expr) (op : Comparison) (rhs : Expr)
  | conn (lhs : Cond) (op : Connective) (rhs : Cond)
  | lnot (rhs : Cond)

inductive Stmt where
  | pass
  | assign (name : String) (expr : Expr)
  | ifte (cond : Cond) (success failure : Stmt)
  | while' (cond : Cond) (body : Stmt)

class Denote (a : Type) where
  domain : Type
  denote : a -> domain

def Int.abs : Int -> Int := ofNat ∘ natAbs
def Int.signum : Int -> Int
  | negSucc _ => negSucc 0
  | ofNat 0 => ofNat 0
  | ofNat (_ + 1) => ofNat 1

open Unary in
instance : Denote Unary where
  domain := Int -> Int
  denote
    | neg => Int.neg
    | abs => Int.abs
    | signum => Int.signum

open Binary in
instance : Denote Binary where
  domain := Int -> Int -> Int
  denote
    | add => Int.add
    | sub => Int.sub
    | mul => Int.mul
    | div => Int.div
    | mod => Int.mod

def Env := String -> Int
def Env.get (σ : Env) (name : String) : Int :=
  σ name
def Env.set (σ : Env) (name : String) (val : Int) : Env :=
  fun name' => if name' = name then val else σ name'

  open Expr Denote in
def denoteExpr (e : Expr) (σ : Env) : Int :=
  match e with
  | var name => σ.get name
  | lit val => val
  | binop lhs op rhs => denote op (denoteExpr lhs σ) (denoteExpr rhs σ)
  | unop op rhs => denote op (denoteExpr rhs σ)

instance : Denote Expr where
  domain := Env -> Int
  denote := denoteExpr

open Comparison in
instance : Denote Comparison where
  domain := Int -> Int -> Bool
  denote
    | eq => (. = .)
    | neq => (. ≠ .)
    | leq => (. ≤ .)
    | geq => (. ≥ .)
    | lt => (. < .)
    | gt => (. > .)

open Connective in
instance : Denote Connective where
  domain := Bool -> Bool -> Bool
  denote
    | land => fun k l => k && l
    | lor => fun k l => k || l
    | lxor => fun k l => k && !l || !k && l

open Cond Denote in
def denoteCond (c : Cond) (σ : Env) : Bool :=
  match c with
  | lit val => val
  | comp lhs op rhs => denote op (denote lhs σ) (denote rhs σ)
  | conn lhs op rhs => denote op (denoteCond lhs σ) (denoteCond rhs σ)
  | lnot rhs => !(denoteCond rhs σ)

instance : Denote Cond where
  domain := Env -> Bool
  denote := denoteCond

def composeRel (g : b -> c -> Prop) (f : a -> b -> Prop) : a -> c -> Prop :=
  fun x z => ∃ y, f x y ∧ g y z

def power (f : a -> a -> Prop) : Nat -> a -> a -> Prop
  | 0 => (. = .)
  | n+1 => composeRel (power f n) f

def star (f : a -> a -> Prop) : a -> a -> Prop :=
  fun x y => ∃ n, power f n x y

open Stmt Denote in
def denoteStmt (stmt : Stmt) (σ σ' : Env) : Prop :=
  match stmt with
  | pass => σ' = σ
  | assign name expr => σ' = σ.set name (denote expr σ)
  | ifte cond success failure =>
    if denote cond σ then
      denoteStmt success σ σ'
    else
      denoteStmt failure σ σ'
  | while' cond body =>
    star (fun σ₁ σ₂ => denote cond σ₁ ∧ denoteStmt body σ₁ σ₂) σ σ' ∧
    ¬ denote cond σ'

instance : Denote Stmt where
  domain := Env -> Env -> Prop
  denote := denoteStmt

open Stmt Denote in
theorem Stmt.deterministic (s : Stmt) (σ σ₁ σ₂ : Env)
  : denote s σ σ₁ -> denote s σ σ₂ -> σ₁ = σ₂ := by
  revert σ σ₁ σ₂
  induction s <;> simp [denote, denoteStmt] <;> intro σ σ₁ σ₂
  case pass =>
    intro h₁ h₂ <;> subst h₁ h₂ <;> simp
  case assign x' e =>
    intro h₁ h₂ <;> subst h₁ h₂ <;> simp
  case ifte c e1 e2 IH1 IH2 =>
    split <;> intro h₀ h₁
    case inl =>
      apply IH1 <;> assumption
    case inr =>
      apply IH2 <;> assumption
  case while' c e IH =>
    simp [star]
    intro ⟨⟨n₁, hp₁⟩, hc₁⟩ ⟨⟨n₂, hp₂⟩, hc₂⟩
    revert σ σ₁ σ₂
    induction n₁ <;> intros σ σ₁ σ₂ hp₁ hc₁ hp₂ hc₂
    case zero =>
      simp [power] at hp₁
      revert σ σ₁ σ₂
      induction n₂ <;> intros σ σ₁ σ₂ hc₂ hp₂ hc₁ hp₁
      case zero =>
        simp [power] at hp₁
        subst hp₁ hp₂ <;> simp
      case succ n₂' IH₂ =>
        simp [power, composeRel] at hp₂
        revert hp₂
        intro ⟨σ₂', ⟨⟨hc₂', _⟩, hp₂'⟩⟩
        subst hp₁
        rewrite [hc₂] at hc₂'
        contradiction
    case succ n₁' IH₁ =>
      revert σ σ₁ σ₂
      induction n₂ <;> intros σ σ₁ σ₂ hp₂ hc₂ hp₁ hc₁
      case zero =>
        simp [power] at hp₁ hp₂
        revert hp₂
        intro ⟨σ₂', ⟨⟨hc₂', _⟩, hp₂'⟩⟩
        subst hp₁
        rewrite [hc₂'] at hc₁
        contradiction
      case succ n₂' IH₂ =>
        simp [power, composeRel] at hp₁ hp₂
        revert hp₁ hp₂
        intro ⟨σ₂', ⟨⟨hc₂', _⟩, hp₂'⟩⟩ ⟨σ₁', ⟨⟨hc₁', _⟩, hp₁'⟩⟩
        
        apply IH₂
        assumption
        assumption
        sorry
        assumption



  sorry