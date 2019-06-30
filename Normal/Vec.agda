module Vec where

open import Agda.Builtin.Equality
open import Agda.Builtin.Nat

data Vec (A : Set) : Nat → Set where
    [] : Vec A 0
    _::_ : {n : Nat} → A → Vec A n → Vec A (suc n)

infixl 12 _++_

_++_ : {A : Set} → {n m : Nat} → Vec A n → Vec A m → Vec A (n + m)
[] ++ r = r
(h :: t) ++  r = h :: (t ++ r)

vapp_assoc :
    {A : Set} {a b c : Nat}
    (x : Vec A a) (y : Vec A b) (z : Vec A c) → (x ++ y) ++ z ≡ x ++ (y ++ z)
vapp_assoc [] = refl
