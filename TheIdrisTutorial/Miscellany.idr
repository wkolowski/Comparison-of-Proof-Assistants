module Miscellany

import Data.Vect

-- Implicit arguments.

-- Auto implicit arguments

isCons' : List a -> Bool
isCons' [] = False
isCons' (x :: _) = True

myhead : (l : List a) -> (p : isCons' l = True) -> a
myhead (x :: _) _ = x

myhead' : (l : List a) -> {auto p : isCons' l = True} -> a
myhead' (x :: _) = x

-- Default implicit arguments

fibonacci : {default 0 lag : Nat} -> {default 1 lead : Nat} -> (n : Nat) -> Nat
fibonacci {lag} Z = lag
fibonacci {lag} {lead} (S n) = fibonacci {lag = lead} {lead = lag + lead} n

-- Implicit conversions

implicit intString : Int -> String
intString = show

test : Int -> String
test x = "Number " ++ x

-- Literate programming: see the file Literate.lidr

-- Foreign function calls TODO

-- Include and linker directives TODO

-- Testing foreign function calls TODO

-- Type Providers

%language TypeProviders

strToType : String -> Type
strToType "Int" = Int
strToType _ = Nat

fromFile : String -> IO (Provider Type)
fromFile filename = do
    Right str <- readFile filename | Left err => pure (Provide Void)
    pure $ Provide (strToType str)

-- Doesn't work.
-- %provide (T : Type) with fromFile "da tajp"

-- foo : T
-- foo = 42

-- Using the FFI

-- Cumulativity

myid : (a : Type) -> a -> a
myid _ x = x

-- Verboten because of universe inconsistency.
--idid : (a : Type) -> a -> a
--idid = myid _ myid