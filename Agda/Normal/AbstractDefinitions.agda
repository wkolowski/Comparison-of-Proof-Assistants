module AbstractDefinitions where

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
            +C : (n m : ℤ) → n +ℤ m ≡ m +ℤ n
            +A : (a b c : ℤ) → (a +ℤ b) +ℤ c ≡ a +ℤ (b +ℤ c)
            inv+- : (k : ℤ) → k +ℤ (-ℤ k) ≡ Zero

abstract
    -- without the keyword 'private' this wouldn't typecheck
    private
        shape-of-Zero : (x : ℤ) (H : x ≡ Zero) → proj₁ x ≡ proj₂ x
        shape-of-Zero (a , b) refl = refl

-- Scope of abstraction

module M1 where
    abstract
        x = 0

    module M2 where
        abstract
            x-is-0 : x ≡ 0
            x-is-0 = refl

module Parent where
    abstract
        module Child where
            y = 0
        x = 0

    y-is-0 : Child.y ≡ 0
    y-is-0 = refl

module Where where
    abstract
        x : Nat
        x = 0

        y : Nat
        y = x
            where
                x≡y : x ≡ 0
                x≡y = refl

module WherePrivate where
    abstract
        x : Nat
        x = proj₁ t
            -- Wouldn't work with "module M where"
            where
                T = Nat × Nat
                t : T
                t = 0 , 1
                p : proj₁ t ≡ 0
                p = refl  