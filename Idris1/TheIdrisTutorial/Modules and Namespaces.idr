module Main

import Interfaces
import public BTree

import Data.Vect

main : IO ()
main = do
    let t = toTree [1, 8, 2, 7, 6, 3, 0]
    print $ BTree.toList t

-- Explicit Namespaces

namespace x
    test : Int -> Int
    test x = 2 * x

namespace y
    test : String -> String
    test x = "2 * " ++ x

-- Parameterised blocks

parameters (x : Nat, y : Nat)
    addAll : Nat -> Nat
    addAll z = x + y + z

parameters (y : Nat, xs : Vect x a)
    data Vects : Type -> Type where
        MkVects : Vect y a -> Vects a

    append : Vects a -> Vect (x + y) a
    append (MkVects ys) = xs ++ ys