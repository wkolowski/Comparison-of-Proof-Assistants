{-# OPTIONS --guardedness #-}

module Coinduction where

open import Agda.Builtin.Equality
open import Data.Product
open import Agda.Builtin.Sigma

record Stream (A : Set) : Set where
    coinductive
    field
        hd : A
        tl : Stream A

open Stream

record _≈_ {A : Set} (s1 s2 : Stream A) : Set where
    coinductive
    field
        hds : hd s1 ≡ hd s2
        tls : tl s1 ≈ tl s2

open _≈_

even : {A : Set} → Stream A → Stream A
hd (even s) = hd s
tl (even s) = even (tl (tl s))

odd : {A : Set} → Stream A → Stream A
hd (odd s) = hd (tl s)
tl (odd s) = odd (tl (tl s))

split : {A : Set} → Stream A → Stream A × Stream A
split s = even s , odd s

unsplit : {A : Set} → Stream A × Stream A → Stream A
hd (unsplit (s1 , s2)) = hd s1
tl (unsplit (s1 , s2)) = unsplit (s2 , tl s1)

-- even and odd are separate, so this needs to be like this.
split-unsplit : {A : Set} (s : Stream A) → unsplit (split s) ≈ s
hds (split-unsplit s) = refl
hds (tls (split-unsplit s)) = refl
tls (tls (split-unsplit s)) = split-unsplit (tl (tl s))

-- Mutually corecursive even and odd.

even2 : {A : Set} → Stream A → Stream A
odd2 : {A : Set} → Stream A → Stream A

hd (even2 s) = hd s
tl (even2 s) = odd2 (tl s)

odd2 s = even2 (tl s)

split2 : {A : Set} → Stream A → Stream A × Stream A
split2 s = even2 s , odd2 s

-- The proof gets simpler because of mutual coinduction.
split-unsplit2 : {A : Set} (s : Stream A) → unsplit (split2 s) ≈ s
hds (split-unsplit2 s) = refl
tls (split-unsplit2 s) = split-unsplit2 (tl s)