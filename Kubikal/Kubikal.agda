{-# OPTIONS --cubical #-}
module Kubikal where

open import Cubical.Core.Everything

open import Cubical.Data.Prod

refl : ∀ {A : Set} {x : A} → x ≡ x
refl {x = x} = λ i → x

sym : ∀ {A : Set} {x y : A} → x ≡ y → y ≡ x
sym p i = p (~ i)

compPath : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
compPath {x = x} p q i = hcomp (λ j → λ { (i = i0) → x ; (i = i1) → q j }) (p i)

data S1 : Set where
    base : S1
    loop : base ≡ base

data Torus : Set where
    base : Torus
    line1 : base ≡ base
    line2 : base ≡ base
    surface : PathP (λ i → line1 i ≡ line1 i) line2 line2

st : S1 × S1 → Torus
st (base , base) = base
st (loop i , S1.base) = line1 i
st (base , loop i) = line2 i
st (loop i , loop j) = surface i j

ts : Torus → S1 × S1
ts base = (base , base)
ts (line1 i) = (loop i , base)
ts (line2 i) = (base , loop i)
ts (surface i j) = (loop i , loop j)

st-ts : (x y : S1) → ts (st (x , y)) ≡  (x , y)
st-ts base base = refl
st-ts base (loop i) = refl
st-ts (loop i) base = refl
st-ts (loop i) (loop j) = refl

ts-st : (t : Torus) → st (ts t) ≡  t
ts-st base = refl
ts-st (line1 i) = refl
ts-st (line2 i) = refl
ts-st (surface i j) = refl

data Bool : Set where
    true : Bool
    false : Bool

data Susp (A : Set) : Set where
    N : Susp A
    S : Susp A
    merid : A → N ≡ S

f : Susp Bool → S1
f N = base
f S = base
f (merid true i) = base
f (merid false i) = loop i

g : S1 → Susp Bool
g base = N
g (loop i) = compPath (merid false) (sym (merid true)) i

-- wut : ∀ {A B : Set} (f : A → B) {x y z : A} (p : x ≡ y) (q : y ≡ z) →
--         (λ i → f (compPath p q i)) ≡ (λ i → compPath (λ i → f p i) (λ i → f q i) i)
-- wut f p q = refl

thm1 : (x : Susp Bool) → g (f x) ≡ x
thm1 N = refl
thm1 S = merid true
thm1 (merid true i) j = merid true (i ∧ j)
thm1 (merid false i) j = ?

thm2 : (x : S1) → f (g x) ≡ x
thm2 base = refl
thm2 (loop i) j = ?