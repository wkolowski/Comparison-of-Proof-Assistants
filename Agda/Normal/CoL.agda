{-# OPTIONS --guardedness #-}

module CoL where

-- This file attempts at a definition of games from Japaridze's Computability Logic.
-- Based on https://github.com/Zeimer/FormalSystems/blob/master/CoL/CoL.v

-- At present, this doesn't even typecheck because Agda seems not to allow
-- coinductive records where one is a parameter of the other.

data Player : Set where
    Machine : Player
    Nature : Player

swapp : Player → Player
swapp Machine = Nature
swapp Nature = Machine

mutual
    record ConstantGame where
        coinductive
        field
            winner : Player
            Move : Set
            who : Move → Player
            next : Move → ConstantGame

    record Winner (g : ConstantGame) (p : Player) : Set where
        coinductive
        field
            WinnerEmpty : (Move g → ⊥) → p = winner g
            WinnerNonempty :
                Move g →
                (Σ _ (λ (move : Move g) → 
                    who g move ≡ p × Winner (next g move) p)) +
                ((move : Labmove g) →
                    who g move ≡ swapp p → Winner (next g move) p)