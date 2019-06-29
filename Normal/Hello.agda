module Hello where

open import IO

open import Agda.Builtin.Unit
open import Agda.Builtin.Bool
open import Agda.Builtin.Nat
open import Agda.Builtin.Equality

if_then_else_ : {A : Set} → Bool → A → A → A
if true then x else y = x
if false then x else y = y

{-# TERMINATING #-}
f91 : Nat → Nat
f91 n = if 100 < n then n - 10 else f91 (f91 (n + 11))

f91_spec1 : f91 110 ≡ f91 110
f91_spec1 = refl

f91_spec : f91 91 ≡ 91
f91_spec = refl

eq? : Nat -> Nat -> Bool
eq? 0 0 = true
eq? 0 _ = false
eq? _ 0 = false
eq? (suc n) (suc m) = eq? n m

main = if eq? (f91 100) 42 then run (putStrLn "Hello World!") else run (putStrLn "Wut!")