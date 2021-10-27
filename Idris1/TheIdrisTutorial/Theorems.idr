module Theorems

%default total

fiveIsFive : 5 = 5
fiveIsFive = Refl

twoPlusTwo : 2 + 2 = 4
twoPlusTwo = Refl

-- The Empty Type

total
disjoint : (n : Nat) -> Z = S n -> Void
disjoint n p = replace {P = P} p ()
    where
        P : Nat -> Type
        P Z = Unit
        P _ = Void

-- Simple Theorems

plusReduces : (n : Nat) -> plus Z n = n
plusReduces n = Refl

plusReducesZ : (n : Nat) -> plus n Z = n
plusReducesZ Z = Refl
plusReducesZ (S k) = cong {f = S} (plusReducesZ k)

plusReducesS : (n : Nat) -> (m : Nat) -> S (plus n m) = plus n (S m)
plusReducesS Z m = Refl
plusReducesS (S n) m = cong (plusReducesS n m)

-- Totality checking

partial
empty1 : Void
empty1 = hd [] where
    partial
    hd : List a -> a
    hd (x :: _) = x

partial
empty2 : Void
empty2 = empty2

-- Hints for Totality

total
qsort : Ord a => List a -> List a
qsort [] = []
qsort (x :: xs) =
    qsort (assert_smaller (x :: xs) (filter (< x) xs)) ++
    x :: qsort (assert_smaller (x :: xs) (filter (>= x) xs))

-- This is bad.
total
wut : Nat -> Void
wut n = wut (assert_smaller n (n + 1))

-- This is even badder.
wut' : Void
wut' = assert_total wut'