import Effects
import Effect.State
import Effect.StdIO
import Effect.System

import Data.Vect

import Control.IOExcept

-- Dependent States

readInt : Eff () [STATE (List Int), STDIO]
readInt = do
    putStrLn $ "Current state: " ++ show !get
    putStr $ "Enter an integer: "
    let x = trim !getStr
    put (cast x :: !get)
    putStrLn $ "Current state: " ++ show !get


readInt2 : Eff () [STATE (Vect n Int), STDIO]
                  [STATE (Vect (S n) Int), STDIO]
readInt2 = do
    putStrLn $ "Current state: " ++ show !get
    putStr $ "Enter an integer: "
    let x = trim !getStr
    putM (cast x :: !get)
    putStrLn $ "Current state: " ++ show !get

-- Result-dependent Effects

readInt3 : Eff Bool [STATE (Vect n Int), STDIO]
                     (\ok => if ok then [STATE (Vect (S n) Int), STDIO]
                                   else [STATE (Vect n Int), STDIO])
readInt3 = do
    putStrLn $ "Current state: " ++ show !get
    putStr $ "Enter an integer: "
    let x = trim !getStr
    case all isDigit (unpack x) of
        False => pureM False
        True => do
            putM (cast x :: !get)
            putStrLn $ "Current state: " ++ show !get
            pureM True

readInt4 : Eff () [STATE (Vect n Int), STDIO]
                    [STATE (Vect (S n) Int), STDIO]
readInt4 = do
    case !readInt3 of
        True => pure ()
        False => readInt4

readInts : (n : Nat) -> Eff () [STATE (Vect m Int), STDIO]
                               [STATE (Vect (n + m) Int), STDIO]
readInts Z = pureM ()
readInts (S n) = do
    readInts n
    readInt2

readInts2 : (n : Nat) -> Eff () [STATE (Vect m Int), STDIO]
                                [STATE (Vect (n + m) Int), STDIO]
readInts2 Z = pureM ()
readInts2 (S n) = do
    readInts2 n
    readInt4

-- File Management

FILE : Type -> EFFECT

data OpenFile : Mode -> Type

open :  (filename : String) ->
        (mode : Mode) ->
        Eff Bool [FILE ()]
                 (\res => [FILE (case res of
                    True => OpenFile mode
                    False => ())])

close : Eff () [FILE (OpenFile m)] [FILE ()]

readLine : Eff String [FILE (OpenFile Read)]

appendLine : String -> Eff () [FILE (OpenFile Append)]

eof : Eff Bool [FILE (OpenFile Read)]

--Handler FILE IO where

readLines : Eff (List String) [FILE (OpenFile Read)]
readLines = aux [] where
    aux : List String -> Eff (List String) [FILE (OpenFile Read)]
    aux acc = if !eof then pure (reverse acc) else aux (!readLine :: acc)

readFile : String -> Eff (Maybe String) [FILE ()]
readFile filename =
    case !(open filename Read) of
        False => pure Nothing
        True => do
            lines <- readLines
            close
            pure . Just $ concat lines

{-
dumpFile : String -> Eff () [STDIO, FILE ()]
dumpFile filename = do
    s <- readFile filename
    case s of
        Nothing => putStrLn "Error!"
        Just text => putStrLn text
-}

{-
dumpFile : String -> Eff () [FILE (), STDIO]
dumpFile filename = do
    True <- open name Read | False => putStrLn "Error!"
    putStrLn (show !readFile)
    close
-}

emain : Eff () [SYSTEM, STDIO]
emain = do
    [prog, arg] <- getArgs | [] => putStrLn "Can't happen!"
                           | [prog] => putStrLn "Not enough arguments!"
                           | _ => putStrLn "Too many arguments!"
    putStrLn $ "Argument is " ++ arg