{-# OPTIONS --prop #-}
module MutualRecursion where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

-- The future will tell what the closed universe is good for.
data U : Set
El : U → Set

data U where
    UNat : U
    UPi : (A : U) (B : El A → U) → U

El UNat = Nat
El (UPi A B) = (x : El A) → El (B x)

-- This is needed.
data _≤_ : Nat → Nat → Prop where
    0≤n : {n : Nat} → 0 ≤ n
    suc≤suc : {n m : Nat} → n ≤ m → suc n ≤ suc m

-- McCarthy's function.
data D : Nat → Set
f : (n : Nat) → D n → Nat

data D where
    D0 : {n : Nat} → 101 ≤ n → D n
    D1 : {n : Nat} (H : n ≤ 100) (d0 : D (n + 11)) (d1 : D (f (n + 11) d0)) → D n

f n (D0 _) = n - 10
f n (D1 _ d0 d1) = f (f (n + 11) d0) d1

-- Chuangjie Xu's ordinals

data ⊥ : Prop where

_≢_ : {A : Set} (x y : A) → Prop
x ≢ y = x ≡ y → ⊥

data Ord : Set
data _<o_ : Ord → Ord → Set
data _≤o_ : Ord → Ord → Set
fst : Ord → Ord
snd : Ord → Ord

data Ord where
    Z : Ord
    cons : (a b : Ord) → a ≤o fst b → Ord

data _<o_ where
    Z< : (n : Ord) → Z ≢ n → Z <o n
    cons<l : {n m : Ord} → fst n <o fst m → n <o m
    cons<r : {n m : Ord} → fst n ≡ fst m → snd n <o snd m → n <o m

data _≤o_ where
    ≤_refl : (n : Ord) → n ≤o n
    ≤_< : {n m : Ord} → n <o m → n ≤o m

fst Z = Z
fst (cons a _ _) = a

snd Z = Z
snd (cons _ b _) = b

<o-trans : {a b c : Ord} → a < b → b < c → a < c
<o-trans (Z< _ H) _ =