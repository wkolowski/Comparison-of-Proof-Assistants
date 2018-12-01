import Data.Vect

-- Running example: Addition of Natural Numbers

pluz : Nat -> Nat -> Nat
pluz Z m = m
pluz (S n) m = S (pluz n m)

-- Equality Proofs

-- Default equality of Idris is heterogeneous and built-in, in contrast to the standard one.
data (==) : (x : a) -> a -> Type where
    Refl : x == x

-- K for homogenous equality is (sadly) provable.
K : {x : a} -> (p : x == x) -> p == Refl
K Refl = Refl

four_eq : 4 = 4
four_eq = Refl

{-
four_eq_five : 4 = 5
four_eq_five = Refl
-}

-- Type checking equality proofs

two_plus_two_eq_four : 2 + 2 = 4
two_plus_two_eq_four = Refl

pluz_reduces_Z : (m : Nat) -> pluz Z m = m
pluz_reduces_Z m = Refl

pluz_reduces_S : (n, m : Nat) -> pluz (S n) m = S (pluz n m)
pluz_reduces_S n m = Refl

-- Heterogeneous Equality

idris_not_php : 2 = "2"
idris_not_php = ?inp

vect_eq_length : (xs : Vect n a) -> (ys : Vect m a) -> (xs = ys) -> n = m
vect_eq_length xs xs Refl = Refl

-- Properties of plus

pluz_comm : (n, m : Nat) -> pluz n m = pluz m n
pluz_assoc : (a, b, c : Nat) -> pluz a (pluz b c) = pluz (pluz a b) c

-- Inductive Proofs

nat_ind : {P : Nat -> Type} -> P Z -> ((n : Nat) -> P n -> P (S n)) -> (n : Nat) -> P n
nat_ind hz _ Z = hz
nat_ind hz hs (S n) = hs n (nat_ind hz hs n)

plus_ind : Nat -> Nat -> Nat
plus_ind n m =
    nat_ind {P = \_ => Nat} m (\_, r => S r) n

pluz_comm n m =
    nat_ind
        {P = \n => (m : Nat) -> pluz n m = pluz m n}
        (nat_ind {P = \m => m = pluz m Z} ?a ?b)
        (\k, hk => nat_ind {P = \_ => (m : Nat) -> S (pluz n m) = pluz m (S n)} ?c ?d m)
            n m