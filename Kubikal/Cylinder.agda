{-# OPTIONS --cubical #-}
module Cylinder where

open import Cubical.Core.Everything

-- Cylinder over A, taken from https://golem.ph.utexas.edu/category/2011/04/homotopy_type_theory_vi.html
data Cylinder (A : Set) : Set where
    inl : A → Cylinder A
    inr : A → Cylinder A
    path : (x : A) → inl x ≡ inr x

-- Cylinder A is equivalent to A.
f : {A : Set} → Cylinder A → A
f (inl x) = x
f (inr x) = x
f (path x i) = x

inl-f : {A : Set} (x : A) → f (inl x) ≡ x
inl-f x i = x

f-inl : {A : Set} (x : Cylinder A) → inl (f x) ≡ x
f-inl (inl x) i = inl x
f-inl (inr x) i = path x i
f-inl (path x j) i = path x (j ∧ i)

-- Mapping cylinder.
data MCylinder {A B : Set} (g : A → B) : Set where
    minl : A → MCylinder g
    minr : B → MCylinder g
    mpath : (x : A) → minl x ≡ minr (g x)

-- A mapping cylinder is equivalent to B.
h : {A B : Set} {g : A → B} (x : MCylinder g) → B
h {g = g} (minl a) = g a
h (minr b) = b
h {g = g} (mpath a i) = g a

minr-h : {A B : Set} {g : A → B} (b : B) → h {g = g} (minr b) ≡ b
minr-h b i = b

h-minr : {A B : Set} {g : A → B} (x : MCylinder g) → minr (h x) ≡ x
h-minr (minl a) i = mpath a (~ i)
h-minr (minr b) i = minr b
h-minr (mpath a j) i = mpath a (j ∨ ~ i)