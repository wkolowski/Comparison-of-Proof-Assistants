import system.io

open nat

def fac : nat → nat
| 0 := 1
| (succ n') := succ n' * fac n'

def qs' (A : Type) (f : A -> A -> bool) : nat -> list A -> list A
| 0 l := l
| _ [] := []
| _ [x] := [x]
| (succ n) (h :: t) :=
    let lesser := qs' n (list.filter (λ a : A, f a h) t),
        greater := qs' n (list.filter (fun a : A, not (f a h)) t)
    in  lesser ++ [h] ++ greater

def leb : nat -> nat -> bool
| 0 _ := tt
| _ 0 := ff
| (succ n) (succ m) := leb n m

def qs {A : Type} (f : A -> A -> bool) (l : list A) :=
    qs' A f (list.length l) l

vm_eval qs leb [9, 5, 4, 16, 42, 56, 7, fac 2, fac 8, fac 5]

theorem leb_0_n : ∀ n : nat, leb 0 n = tt :=
begin
    intros, unfold leb, destruct n,
        intro H, rw H, simp, trivial,
        intros m H, rw H, trivial
end

def main : io unit := do
    name <- get_line,
    put_str_ln $ "Hello " ++ name

open applicative

print applicative
