{-# OPTIONS --prop #-}
module Irrelevance where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data _≤_ : Nat → Nat → Prop where
    Z≤n : {n : Nat} → zero ≤ n
    S≤S : {n m : Nat} → n ≤ m → suc n ≤ suc m

postulate
    p1 : zero ≤ 42
    p2 : zero ≤ 42

data SList : Nat → Set where
    snil : (n : Nat) → SList n
    scons : {h n : Nat} → h ≤ n → (t : SList n) → SList h

l1 : SList 0
l1 = scons p1 (snil 42)

l2 : SList 0
l2 = scons p2 (snil 42)

thm : l1 ≡ l2
thm = refl