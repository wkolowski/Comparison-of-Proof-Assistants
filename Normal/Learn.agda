module Learn where

open import Agda.Builtin.Nat
open import Data.Product
open import Agda.Builtin.Equality

-- Abstract definitions.

abstract

    ℤ : Set
    ℤ = Nat × Nat

    Zero : ℤ
    Zero = 0 , 0

    One : ℤ
    One = 1 , 0

    _+ℤ_ : ℤ → ℤ → ℤ
    (a , b) +ℤ (c , d) = a + c , b + d

    -- infixr 25 _+ℤ_

    -ℤ_ : ℤ → ℤ
    -ℤ (a , b) = b , a

    _≡ℤ_ : ℤ → ℤ → Set
    (a , b) ≡ℤ (c , d) = a + d ≡ b + c
    
    private
        postulate
            +C : (a b c : ℤ) → (a +ℤ b) +ℤ c ≡ a +ℤ (b +ℤ c)
            inv+- : (k : ℤ) → k +ℤ (-ℤ k) ≡ Zero

-- Coinduction

