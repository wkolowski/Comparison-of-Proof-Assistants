module Levels where

open import Agda.Primitive
open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat

data Unit : Set where
    tt : Unit

-- Monomorphic at level 0.
-- data _×_ (A B : Set) : Set where
--     _,_ : A → B → A × B

data _×_ {l1 l2 : Level} (A : Set l1) (B : Set l2) : Set (l1 ⊔ l2) where
    _,_ : A → B → A × B

-- Monomorphic at level 0.
-- data List (A : Set) : Set where
--     [] : List A
--     _::_ : A → List A → List A

data List {l : Level} (A : Set l) : Set l where
     [] : List A
     _::_ : A → List A → List A

infixr 5 _::_
infixr 4 _,_
infixr 2 _×_ 

t1 : Set
t1 = Bool

-- Looks like Nat is a Set (i.e. Set 0), not Set1 or Set2.
-- t2 : Set2
-- t2 = Nat

t2 : Set
t2 = Nat

-- Set1 != Set
-- t3 : Set
-- t3 = List Set

prod : List Set → Set
prod [] = Unit
prod (A :: sets) = A × prod sets

t3 : Set
t3 = List Nat

t4 : Set1
t4 = List Set

t5 : Set2
t5 = List Set1

map1 : {l1 l2 : Level} {A : Set l1} {B : Set l2} (f : A → B) (l : List A) → List B
map1 f [] = []
map1 f (h :: t) = f h :: map1 f t

map2 : ∀ {l1 l2} {A : Set l1} {B : Set l2} (f : A → B) (l : List A) → List B
map2 f [] = []
map2 f (h :: t) = f h :: map2 f t

data Unit' (l : Level) : Set l where
    tt : Unit' l

t6 : (l : Level) → Set l
t6 = Unit'

largeType : Setω
largeType = (l : Level) → Set l

badList : List ((l : Level) → Set l)
badList = Unit' :: []