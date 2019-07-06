{-# OPTIONS --prop #-}
module Propp where

open import Agda.Builtin.Nat
open import Agda.Builtin.Equality
open import Agda.Primitive

data ⊥ : Prop where

data Unit : Prop where
    tt : Unit

absurd : (A : Set) → ⊥ → A
absurd A ()

data buul : Prop where
    truu : buul
    faals : buul

-- Doesn't work because ≡ takes arguments from a type in Set.
-- isContr-buul : (x y : buul) → x ≡ y
-- isContr-buul _ _ = refl

only-one-absurdity : {A : Set} (x y : ⊥) → absurd A x ≡ absurd A y
only-one-absurdity _ _ = refl

isContr-buul : {A : Set} (f : buul → A) (x y : buul) → f x ≡ f y
isContr-buul f x y = refl

data _≤_ : Nat → Nat → Prop where
    Z≤n : {n : Nat} → zero ≤ n
    S≤S : {n m : Nat} → n ≤ m → suc n ≤ suc m

_≤'_ : Nat → Nat → Prop
zero ≤' _ = Unit
_ ≤' zero = ⊥
suc n ≤' suc m = n ≤' m

≤-to-≤' : {n m : Nat} → n ≤ m → n ≤' m
≤-to-≤' Z≤n = tt
≤-to-≤' (S≤S H) = ≤-to-≤' H

≤'-to-≤ : (n m : Nat) → n ≤' m → n ≤ m
≤'-to-≤ zero _ _ = Z≤n
≤'-to-≤ (suc _) zero ()
≤'-to-≤ (suc n) (suc m) H = S≤S (≤'-to-≤ n m H)

data Wrap (P : Prop) : Set where
    Wrap' : P → Wrap P

≤-to-≤'-to-≤ : {n m : Nat} (H : n ≤ m) → Wrap' (≤'-to-≤ n m (≤-to-≤' H)) ≡ Wrap' H
≤-to-≤'-to-≤ _ = refl

≤'-to-≤-to-≤' : {n m : Nat} (H : n ≤' m) → Wrap' (≤-to-≤' (≤'-to-≤ n m H)) ≡ Wrap' H
≤'-to-≤-to-≤' _ = refl

≤'-ind :
    (P : (n m : Nat) → Set)
    (PZ : (n : Nat) → P zero n)
    (PS : (n m : Nat) → P n m → P (suc n) (suc m)) →
        (n m : Nat) → n ≤' m → P n m
≤'-ind P PZ PS zero n _ = PZ n
≤'-ind P PZ PS (suc _) zero ()
≤'-ind P PZ PS (suc n) (suc m) H = PS n m (≤'-ind P PZ PS n m H)

record Fin (n : Nat) : Set where
    constructor _[_]
    field
        ⟦_⟧ : Nat
        proof : suc ⟦_⟧ ≤' n
open Fin

Fin-≡ : {n : Nat} (x y : Fin n) → ⟦ x ⟧ ≡ ⟦ y ⟧ → x ≡ y
Fin-≡ _ _ refl = refl

data True {l : Level} : Prop l where
    I : True

data Trunc (A : Set) : Prop where
    trunc : A → Trunc A

Trunc-ind : {A : Set} {P : Prop} → (A → P) → Trunc A → P
Trunc-ind f (trunc x) = f x

data _≣_ {A : Set} (x : A) : A → Prop where
    refl' : x ≣ x

0≠1 : 0 ≣ 1 → ⊥
0≠1 ()

1-is-1 : 1 ≣ 1
1-is-1 = refl'

-- No J - how sad.