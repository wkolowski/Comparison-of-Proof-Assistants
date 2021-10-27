{-# OPTIONS --cubical --prop #-}
module Kubikal where

open import Cubical.Core.Everything

open import Cubical.Data.Empty
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

-- thm1 : (x : Susp Bool) → g (f x) ≡ x
-- thm1 N = refl
-- thm1 S = merid true
-- thm1 (merid true i) j = merid true (i ∧ j)
-- thm1 (merid false i) j = ?

-- thm2 : (x : S1) → f (g x) ≡ x
-- thm2 base = refl
-- thm2 (loop i) j = ?

-- Let's try to prove that loop <> refl

h : S1 → Bool
h base = true
h (loop i) = true

h-const : (x : S1) → h x ≡ true
h-const base = refl
h-const (loop i) = refl

h-const' : h ≡ λ _ → true
h-const' i = λ x → h-const x i

-- loop-not-refl : loop ≡ refl → ⊥
-- loop-not-refl

data ℤ : Set where
    Z : ℤ
    S : ℤ → ℤ
    P : ℤ → ℤ
    SP : (k : ℤ) → S (P k) ≡ k
    PS : (k : ℤ) → P (S k) ≡ k
    ℤ-isSet : {k l : ℤ} (p q : k ≡ l) → p ≡ q

neg : ℤ → ℤ
neg Z = Z
neg (S a) = P (neg a)
neg (P a) = S (neg a)
neg (SP a i) = PS (neg a) i
neg (PS a i) = SP (neg a) i
neg (ℤ-isSet p q i j) = ℤ-isSet (λ k → neg (p k)) (λ k → neg (q k)) i j

neg-neg : (a : ℤ) → neg (neg a) ≡ a
neg-neg Z i = Z
neg-neg (S a) i = S (neg-neg a i)
neg-neg (P a) i = P (neg-neg a i)
neg-neg (SP a i) j = SP (neg-neg a j) i
neg-neg (PS a i) j = PS (neg-neg a j) i
neg-neg (ℤ-isSet p q i j) k = ℤ-isSet (λ l → neg-neg (p l) k) (λ l → neg-neg (q l) k) i j

-- normalize : ℤ → ℤ
-- normalize Z = Z
-- normalize (S a) with (normalize a)
-- normalize (S a) | Z = S Z
-- normalize (S a) | (S a') = S (S a')
-- normalize (S a) | (P a') = a'
-- normalize (S a) | (SP a' i) = ?
-- normalize (S a) | (PS a' i) = PS (S a') i
-- normalize (S a) | (ℤ-isSet p q i j) = S (ℤ-isSet p q i j)
-- normalize (P a) with (normalize a)
-- normalize (P a) | Z = P Z
-- normalize (P a) | (S a') = a'
-- normalize (P a) | (P a') = P (P a')
-- normalize (P a) | (SP a' i) = P (SP a' i)
-- normalize (P a) | (PS a' i) = P (PS a' i)
-- normalize (P a) | (ℤ-isSet p q i j) = P (ℤ-isSet p q i j)
-- normalize (SP a i) = normalize a
-- normalize (PS a i) = normalize a
-- normalize (ℤ-isSet p q i j) =
--     ℤ-isSet (λ k → normalize (p k)) (λ k → normalize (q k)) i j

add : ℤ → ℤ → ℤ
add a Z = a
add a (S b) = S (add a b)
add a (P b) = P (add a b)
add a (SP b i) = SP (add a b) i
add a (PS b i) = PS (add a b) i
add a (ℤ-isSet p q i j) = ℤ-isSet (λ k → add a (p k)) (λ k → add a (q k)) i j

neg-add : (a b : ℤ) → neg (add a b) ≡ add (neg a) (neg b)
neg-add a Z     i = neg a
neg-add a (S b) i = P (neg-add a b i)
neg-add a (P b) i = S (neg-add a b i)
neg-add a (SP b i) j = PS (neg-add a b j) i
neg-add a (PS b i) j = SP (neg-add a b j) i
neg-add a (ℤ-isSet p q i j) k = ℤ-isSet (λ l → neg-add a (p l) k) (λ l → neg-add a (q l) k) i j

sub : ℤ → ℤ → ℤ
sub a b = add a (neg b)

-- neg-sub : (a b : ℤ) → neg (sub a b) ≡ sub b a
-- neg-sub a b i = neg-add a (neg b)

-- mul : ℤ → ℤ → ℤ
-- mul a Z = ℤ
-- mul a (S b) = add (mul a b) a
-- mul a (P b) = sub (mul a b) a
-- mul a (SP b i) = 

data Unit : Set where
    tt : Unit

isProp : (A : Set) → Set
isProp A = (x y : A) → x ≡ y

isSet : (A : Set) → Set
isSet A = {x y : A} (p q : x ≡ y) → p ≡ q

-- isProp-isSet : {A : Set} → isProp A → isSet A
-- isProp-isSet f {x = x} {y = y} p q i j = x

-- isProp-isProp : {A : Set} → isProp (isProp A)
-- isProp-isProp {A = A} f g i = λ x y → f (f x y i) (g x y i) i

isProp-Unit : isProp Unit
isProp-Unit tt tt = refl

Unit-K : {x : Unit} (p : x ≡ x) → p ≡ (λ i → x)
Unit-K {x = tt} p i j = isProp-Unit (p j) tt i

Unit-isSet : {x y : Unit} (p q : x ≡ y) → p ≡ q
Unit-isSet {x = tt} {y = tt} p q i j = compPath (Unit-K p) (sym (Unit-K q)) i j

data SadCircle : Set where
    base : SadCircle
    loop : base ≡ base
    SadCircle-isSet : {x y : SadCircle} (p q : x ≡ y) → p ≡ q

u2s : Unit → SadCircle
u2s tt = base

s2u : SadCircle → Unit
s2u base = tt
s2u (loop i) = tt
s2u (SadCircle-isSet p q i j) =
     Unit-isSet (λ k → s2u (p k)) (λ k → s2u (q k)) i j

u2s2u : (x : Unit) → s2u (u2s x) ≡ x
u2s2u tt = refl

-- s2u2s : (x : SadCircle) → u2s (s2u x) ≡ x
-- s2u2s base = refl
-- s2u2s (loop i) j = loop (i ∧ j)

data Wut (A B : Set) : Set where
    inl : A → Wut A B
    inr : B → Wut A B
    glu : (a : A) (b : B) → inl a ≡ inr b

u2w : Unit → Wut Unit Unit
u2w tt = inl tt

w2u : Wut Unit Unit → Unit
w2u (inl tt) = tt
w2u (inr tt) = tt
w2u (glu tt tt i) = tt

u2w2u : (x : Unit) → w2u (u2w x) ≡ x
u2w2u tt = refl

-- Finally a slight success!
w2u2w : (x : Wut Unit Unit) → u2w (w2u x) ≡ x
w2u2w (inl tt) = refl
w2u2w (inr tt) = glu tt tt
w2u2w (glu tt tt i) = λ j → glu tt tt (j ∧ i)