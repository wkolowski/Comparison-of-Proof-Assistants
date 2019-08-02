{-# OPTIONS --cubical #-}
module Cubical where

open import Cubical.Core.Everything

-- The interval and path types
wut1 : ∀ {l} (A : I → Set l) → A i0 → A i1 → Set l
wut1 = PathP

wut2 : ∀ {l} (A : Set l) → A → A → Set l
wut2 = Path

refl : {A : Set} {x : A} → Path A x x
refl {x = x} = λ i → x

Square : {A : Set} {tl tr bl br : A} (l : tl ≡ bl) (r : tr ≡ br) (t : tl ≡ tr) (b : bl ≡ br) → Set
Square l r t b = PathP (λ i → l i ≡ r i) t b

sym : {A : Set} {x y : A} (p : x ≡ y) → y ≡ x
sym p = λ i → p (~ i)

cong : {A : Set} {B : A → Set} (f : (x : A) → B x) {x y : A} (p : x ≡ y) → PathP (λ i → B (p i)) (f x) (f y)
cong f p = λ i → f (p i)

sym_refl : {A : Set} {x : A} → sym (refl {x = x}) ≡ refl
sym_refl = refl

sym_sym : {A : Set} {x y : A} (p : x ≡ y) → sym (sym p) ≡ p
sym_sym p = refl

cong_refl : {A : Set} {B : A → Set} (f : (x : A) → B x) {x : A} → cong f (refl {x = x}) ≡ refl
cong_refl _ = refl

cong_id : {A : Set} {x y : A} (p : x ≡ y) → cong (λ x → x) p ≡ p
cong_id _ = refl

cong_comp :
    {A B C : Set} (f : A → B) (g : B → C) {x y : A} (p : x ≡ y) →
    cong g (cong f p) ≡ cong (λ x → g (f x)) p
cong_comp f g p = refl

funext : {A : Set} {B : A → Set} (f g : (x : A) → B x) → ((x : A) → f x ≡ g x) → f ≡ g
funext f g p = λ i → λ x → p x i

-- Transport
