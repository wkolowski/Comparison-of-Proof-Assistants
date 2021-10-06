import system.io

def main : io unit := do
    name <- get_line,
    put_str_ln $ "Hello " ++ name

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
        greater := qs' n (list.filter (λ a : A, not (f a h)) t)
    in  lesser ++ [h] ++ greater

def qs {A : Type} (f : A -> A -> bool) (l : list A) :=
    qs' A f (list.length l) l

def leb : nat -> nat -> bool
| 0 _ := tt
| _ 0 := ff
| (succ n) (succ m) := leb n m

vm_eval qs leb [9, 5, 4, 16, 42, 56, 7, fac 2, fac 8, fac 5]

inductive sorted {A : Type} (R : A -> A -> Prop) : list A -> Prop
| sorted_nil : sorted []
| sorted_singl : forall x : A, sorted [x]
| sorted_cons : forall (x y : A) (l : list A),
    R x y -> sorted (y :: l) -> sorted (x :: y :: l)

def nat_ind2 (P : nat -> Prop) (H0 : P 0) (H1 : P 1)
    (HSS : forall n : nat, P n -> P (n + 2))
    : forall n : nat, P n
| 0 := H0
| 1 := H1
| (n + 2) := HSS n (nat_ind2 n)

inductive even : nat -> Prop
| even0 : even 0
| evenSS : forall n : nat, even n -> even (n + 2)

example : even 0 :=
begin
    constructor
end

example : even 2 :=
begin
    constructor, constructor
end

example : even 666 :=
begin
    constructor,
    repeat { constructor }
end

def ins {A : Type} (cmp : A -> A -> bool)
    : A -> list A -> list A
| x [] := [x]
| x (h :: t) := if cmp x h
    then x :: h :: t
    else h :: ins x t

def fold {A B : Type} (f : A -> B -> B) (b : B)
    : list A -> B
| [] := b
| (h :: t) := f h (fold t)

vm_eval fold (add) 0 [1, 2, 3]

def sort {A : Type} (cmp : A -> A -> bool)
    (l : list A) : list A := fold (ins cmp) [] l

def geb : nat -> nat -> bool
| _ 0 := tt
| (n + 1) (m + 1) := geb n m
| _ _ := ff

vm_eval sort geb [22, 5, 6, 1, 989, 23, 5, 234, 78, 12]

def injective {A B : Type} (f : A -> B) : Prop :=
    forall x x' : A, f x = f x' -> x = x'

def surjective {A B : Type} (f : A -> B) : Prop :=
    forall b : B, exists a : A, f a = b

def bijective {A B : Type} (f : A -> B) : Prop :=
    injective f /\ surjective f

open nat

def nat_to_list_unit : nat -> list unit
| 0 := []
| (succ n) := unit.star :: nat_to_list_unit n

def len {A : Type} : list A -> nat
| [] := 0
| (h :: t) := succ $ len t

example : bijective nat_to_list_unit :=
begin
    unfold bijective, unfold injective,
    unfold surjective,
    split,
        intro n, induction n with n' IH1,
            intro m, induction m with m' IH2,
                intro H, trivial,
                intro H, simp at H,
                    unfold nat_to_list_unit at H,
                    contradiction,
            intro m, induction m with m' IH2,
                intro H, simp at H,
                    unfold nat_to_list_unit at H,
                    contradiction,
                intro H, rw IH1,
                    unfold nat_to_list_unit at H,
                    injection H, assumption,
        intro b, existsi (len b),
        induction b with h t IH,
            trivial,
            unfold len, unfold nat_to_list_unit,
                destruct h, intro Hh, rw [Hh, IH],
end

eval monad.filter (fun _, [ff, tt]) [1, 2, 3]

def fibs' : nat -> nat -> nat -> list nat
| 0 a b := []
| (nat.succ n) a b := a :: fibs' n b (a + b)

def fibs (n : nat) : list nat := fibs' n 0 1

eval fibs 15

def hd {A : Type} : list A -> option A
| [] := none
| (h :: _) := some h

def tail {A : Type} : list A -> option (list A)
| [] := none
| (_ :: t) := some t

print monad.lift₂

def liftM2 {M : Type -> Type} [_inst_1 : monad M] {A B C : Type}
    (f : A -> B -> C) (ma : M A) (mb : M B) : M C :=
    ma >>= λa : A, mb >>= λb : B, return $ f a b

def uncons {A : Type} (l : list A) : option (A × list A)
    := liftM2 (prod.mk) (hd l) (tail l)

eval uncons [1, 2, 5]

open nat

def facts' : nat -> nat -> nat -> list nat -> list nat
| 0 _ f fs := f :: fs
| (succ fuel) n f fs :=
    facts' fuel (succ n) (n * f) (f :: fs)

def facts (n : nat) : list nat :=
    list.reverse $ facts' n 1 1 []

def plus : nat -> nat -> nat
| 0 m := m
| (succ n) m := succ (plus n m)

theorem add_is_plus : ∀ n m : nat,
    n + m = plus n m :=
begin
intro n, induction n with n' IHn,
    intro m, induction m with m' IHm,
        trivial,
        simp, unfold plus, trivial,
    intro m, induction m with m' IHm,
        simp, unfold plus, rw -IHn, trivial,
        unfold plus, rw -IHn, rw succ_add,
end

open nat
open list

def gcd' : nat -> nat -> nat -> option nat
| 0 a b := none
| _ a 0 := some a
| _ 0 b := some b
| (succ n) a b := gcd' n b (mod a b)

def gcd (a b : nat) : option nat :=
    gcd' a a b

def product := list.foldr mul 1

def range1 : nat -> list nat
| 0 := []
| (succ n) := (succ n) :: range1 n

def range' : nat -> nat -> list nat
| 0 0 := [0]
| 0 (succ b) := b :: range' 0 b
| _ 0 := []
| a (succ b) :=
    if a > succ b then [] else succ b :: range' a b
def myRange (a b : nat) : list nat
    := reverse $ range' a b

eval range1 12
eval myRange 21 5
vm_eval gcd (product $ myRange 13 20)
    (product $ myRange 17 16)

open monad
open nat

def iterM {M : Type -> Type} [_inst : monad M]
    {A : Type} (f : A -> M A) : nat -> A -> M A
| 0 x := return x
| (succ n) x := f x >>= iterM n

def replicateM {M : Type -> Type} [_inst : monad M]
    {A : Type} : nat -> M A -> M (list A)
| 0 _ := return []
| (succ n) ma := do
    h ← ma,
    t ← replicateM n ma,
    return $ h :: t

eval replicateM 3 [1, 2]


def injective {A B : Type} (f : A → B) : Prop
    := ∀ x x' : A, f x = f x' → x = x'

def injective' {A B : Type} (f : A → B) : Prop
    := ∀ x x' : A, x ≠ x' → f x ≠ f x'

theorem injectives_equiv_classical :
    ∀ (A B : Type) (f : A → B)
    (EM : ∀ P : Prop, P ∨ ¬ P),
    injective f ↔ injective' f :=
begin
    unfold injective, unfold injective', unfold iff,
    intros, split,
        intros, intro, apply a_1, apply a, assumption,
        intros, destruct (EM (x = x')),
            intro, assumption,
            intro, exfalso, apply a,
                exact a_2,
                assumption
end

open nat

theorem succ_inj : injective succ :=
begin
    unfold injective, intros, injection a,
    assumption
end

theorem add_k_inj : ∀ k : nat,
    injective (λ n : nat, k + n) :=
begin
    intro, unfold injective, induction k with k' Hk',
        intros, simp at a, assumption,
        intros, apply Hk', rw succ_add at a,
            rw succ_add at a, injection a,
            assumption
end

def surjective {A B : Type} (f : A -> B) : Prop
    := ∀ b : B, ∃ a : A, f a = b

theorem pred_sur : surjective pred :=
begin
    unfold surjective, intro, existsi (succ b),
    trivial
end

theorem S_not_sur : ¬ surjective succ :=
begin
    unfold not, unfold surjective, intro H,
    destruct (H 0), intros, contradiction
end

def bijective {A B : Type} (f : A → B) : Prop
    := injective f ∧ surjective f

def bijective' {A B : Type} (f : A → B) : Prop
    := ∀ b : B, ∃! a : A, f a = b

theorem bijective_equiv : ∀ (A B : Type) (f : A → B),
    bijective f ↔ bijective' f :=
begin
    unfold bijective, unfold bijective',
    unfold injective, unfold surjective,
    intros, unfold iff, split,
        intros H b, cases H with Hinj Hsur,
            cases (Hsur b) with a H,
            apply (exists.intro a), split,
                assumption,
                intros y Hy, apply Hinj,
                    rw [H, Hy],
        intro Hbij, split,
            intros x x' H, cases (Hbij (f x)) with a H,
                cases H with Heq Huniq,
                rw (Huniq x), rw (Huniq x'), rw H, trivial,
            intros, cases (Hbij b) with a H,
                cases H with Heq Huniq, existsi a, assumption
end
                
def empty_sum_A {A : Type} : empty ⊕ A → A
| (sum.inl e) := match e with end
| (sum.inr a) := a

theorem empty_sum_A_bij : ∀ A : Type,
    bijective (@empty_sum_A A) :=
begin
    unfold bijective, unfold injective,
    unfold surjective, intro, split,
        intros, cases x with e a,
            destruct e,
            cases x' with e a',
                destruct e,
                unfold empty_sum_A at a, rw a,
        intro a, existsi (sum.inr a),
            trivial,
            exact empty
end
