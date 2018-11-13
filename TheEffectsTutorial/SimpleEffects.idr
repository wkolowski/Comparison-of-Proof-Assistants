-- Console I/O

import Data.Vect

import Effects
import Effect.State
import Effect.StdIO
import Effect.Exception
import Effect.Random
import Effect.System
import Effect.Select

hello : Eff () [STDIO]
hello = do
    putStr "Name? "
    putStrLn $ "Hello " ++ trim !getStr ++ "!"

hellos : Eff () [STATE Nat, STDIO]
hellos = do
    update S
    putStr "Name? "
    putStrLn $ ("Hello " ++ trim !getStr ++ "! You're the " ++
                show !get ++ "-th person I've said 'Hello' to!")
    hellos
    pure ()

main1 : IO ()
main1 = runInit [42, ()] hellos

-- Exceptions TODO

-- Random numbers

guess : Int -> Eff () [STDIO]
guess k = do
    putStr "Make a guess: "
    case compare (the Int (cast (trim !getStr))) k of
        LT => do putStrLn "Too small!"; guess k
        EQ => do putStrLn "You win!"; pure ()
        GT => do putStrLn "Too big!"; guess k

game : Eff () [RND, SYSTEM, STDIO]
game = do
    srand !time
    guess $ fromInteger !(rndInt 0 100)
    pure ()

main : IO ()
main = run game

-- Nondeterminism

triple : Int -> Eff (Int, Int, Int) [SELECT, EXCEPTION String]
triple n = do
    z <- select [1..n]
    y <- select [1..z]
    x <- select [1..y]
    if (x * x + y * y == z * z)
    then pure (x, y, z)
    else raise "Wut"

-- vadd revisited

vadd : Vect n Int -> Vect n Int -> Vect n Int
vadd [] [] = []
vadd (x :: xs) (y :: ys) = x + y :: vadd xs ys

vadd_check : Vect n Int -> Vect m Int -> Eff (Vect m Int) [EXCEPTION String]
vadd_check {n} {m} xs ys with (decEq n m)
    vadd_check {n} {m = n} xs ys | Yes Refl = pure (vadd xs ys)
    vadd_check {n} {m} xs ys | No _ = raise "Length mismatch"

parseInt : String -> Eff Int [EXCEPTION String]
parseInt str =
    case the Int $ cast str of
        0 => if str == "0" then pure 0 else raise "Lol can't parse"
        n => pure n

parseList : (String -> Eff a [EXCEPTION String]) -> String -> Eff (List a) [EXCEPTION String]
parseList f str = aux f (words str) where
    aux : (String -> Eff a [EXCEPTION String]) -> List String -> Eff (List a) [EXCEPTION String]
    aux _ [] = pure []
    aux f (x :: xs) = do --[| (::) (f x) (aux xs) |]
        h <- f x
        t <- aux f xs
        pure $ h :: t

listToVec : (l : List a) -> Vect (length l) a
listToVec [] = []
listToVec (x :: xs) = x :: listToVec xs

readVect : Eff (n ** Vect n Int) [STDIO, EXCEPTION String]
readVect = do
    str <- getStr
    --l <- the (Maybe _) $ run $ parseList parseInt str
    l <- parseList parseInt str
    pure $ (length l ** listToVec l)

do_vadd : Eff () [STDIO, EXCEPTION String]
do_vadd = do
    putStr "Enter vector 1: "
    (_ ** v1) <- readVect
    putStr "Enter vector 2: "
    (_ ** v2) <- readVect
    v <- vadd_check v1 v2
    putStr "Aaaand the result is "
    printLn v

-- Example: An Epression Calculator

data Expr
    = Var String
    | Val Integer
    | Add Expr Expr

Env : Type
Env = List (String, Integer)

env : Eff Env [STATE Env]
env = get

eval : Expr -> Eff Integer [EXCEPTION String, STATE Env]
eval (Val k) = pure k
eval (Var v) = do
    case lookup v !env of
        Nothing => raise $ "Variable " ++ v ++ " is undefined"
        Just k => pure k
eval (Add e1 e2) = [| (+) (eval e1) (eval e2) |]
--eval (Add e1 e2) = pure $ !(eval e1) + !(eval e2)

--runEval : Env -> Expr -> Eff Integer [EXCEPTION String]
runEval : Env -> Expr -> Maybe Integer
runEval env e = run (eval' e) where
    eval' : Expr -> Eff Integer [EXCEPTION String, STATE Env]
    eval' e = do
        put env
        eval e
{-
parseInteger : String -> Eff Integer [EXCEPTION String]
parseInteger str =
    case cast Integer str of
        0 => if str == "0" then pure 0 else raise "Lol can't parse"
        n => pure n
-}
