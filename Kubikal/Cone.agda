{-# OPTIONS --cubical #-}
module Cone where

open import Cubical.Core.Everything

data Option (A : Set) : Set where
    None : Option A
    Some : A → Option A

data MCone {A B : Set} (f : A → B) : Set where
    tip : MCone f
    inb : B → MCone f
    path : (x : A) → tip ≡ inb (f x)

-- cone : {A B : Set} (f : A → B) → Option B → MCone f
-- cone f None = tip
-- cone f (Some b) = inb b

uncone : {A B : Set} {f : A → B} (b : B) (h : (x : A) → b ≡ f x) → MCone f → B
uncone b _ tip = b
uncone _ _ (inb b') = b'
uncone _ h (path x i) = h x i

inb-uncone :
    {A B : Set} {f : A → B} (b : B) (h : (x : A) → b ≡ f x) (x : B) → uncone b h (inb x) ≡ x
inb-uncone _ _ x = λ i → x

cat : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
cat {x = x} p q i = hcomp (λ j → λ { (i = i0) → x ; (i = i1) → q j }) (p i)

-- meh, this is so hard
uncone-cone :
    {A B : Set} {f : A → B} (a : A) (b : B) (h : (x : A) → b ≡ f x) (x : MCone f) → x ≡ inb (uncone b h x)
uncone-cone a b h tip = cat (path a) (λ i → inb (h a (~ i)))
uncone-cone a b h (inb b') = λ i → inb b'
uncone-cone a b h (path x j) = cat (λ i → path x (j ∨ i)) (λ i → inb (h x (j ∨ ~ i)))

-- path x j ≡ inb (h x j)
