-- This shit doesn't work.

import Effects
import Effect.StdIO
import Effect.System
import Effect.Random

import Prelude.Strings
import Data.Vect

-- Step 1: Game State

data GState = Running Nat Nat | NotRunning

data Mystery : GState -> Type

-- Step 2: Game Rules

letters : String -> List Char
letters = nub . unpack . trim

data MysteryRules : Effect where
    Guess : (x : Char) ->
            sig MysteryRules Bool
                (Mystery (Running (S g) (S w)))
                (\inword => if inword
                            then Mystery (Running (S g) w)
                            else Mystery (Running g (S w)))
    Won : sig MysteryRules () (Mystery (Running g 0)) (Mystery NotRunning)
    Lost : sig MysteryRules () (Mystery (Running 0 w)) (Mystery NotRunning)
    NewWord : (n : Nat) -> (w : String) ->
              sig MysteryRules () (Mystery NotRunning) (Mystery (Running n (length (letters w))))
    Get : sig MysteryRules String (Mystery h)

MYSTERY : GState -> EFFECT
MYSTERY h = MkEff (Mystery h) MysteryRules

-- Step 3: Implement Rules

data Mystery : GState -> Type where
    Init : Mystery NotRunning
    GameWon : (word : String) -> Mystery NotRunning
    GameLost : (word : String) -> Mystery NotRunning
    MkG : (word : String) -> (guesses : Nat) -> (got : List Char) -> (missing : Vect m Char) ->
            Mystery (Running guesses m)

initState : (n : Nat) -> (w : String) -> Mystery (Running n (length (letters w)))
initState n w = MkG w n [] (fromList (letters w))

data IsElem : a -> Vect n a -> Type where
    First : IsElem x (x :: _)
    Later : IsElem x xs -> IsElem x (y :: xs)

isElem : (DecEq a) => (x : a) -> (xs : Vect n a) -> Maybe (IsElem x xs)
isElem x [] = Nothing
isElem x (y :: ys) with (decEq x y)
    isElem x (x :: ys) | Yes Refl = Just First
    isElem x (_ :: ys) | No =
        case isElem x ys of
            Nothing => Nothing
            Just p => Just (Later p)

isElem' : (DecEq a) => (x : a) -> (xs : Vect n a) -> Dec (IsElem x xs)
isElem' x [] = No ?a
isElem' x (y :: ys) with (decEq x y)
    isElem' x (x :: ys) | Yes Refl = Yes First
    isElem' x (_ :: ys) | No =
        case isElem' x ys of
            No p => No ?b
            Yes p => Yes (Later p)

shrink : (xs : Vect (S n) a) -> IsElem x xs -> Vect n a
shrink (x :: xs) First = xs
shrink [x] (Later p) impossible
shrink (x :: y :: xs) (Later p) = x :: shrink (y :: xs) p

Handler MysteryRules m where
    handle st Get k = k "" {-(show st)-} st
    handle st (NewWord n w) k = k () (initState n w)
    handle (MkG w g got []) Won k = k () (GameWon w)
    handle (MkG w Z got m) Lost k = k () (GameLost w)
    handle (MkG w (S g) got m) (Guess x) k =
        case isElem x m of
            Nothing => k False (MkG w _ got m)
            Just p => k True (MkG w _ (x :: got) (shrink m p))

-- Step 4: Implement Interfaces

game : Eff () [MYSTERY (Running (S g) w), STDIO] [MYSTERY NotRunning, STDIO]
game {w = Z} = Won
game {w = S _} = do
    putStrLn !Get
    putStr "Enter guess: "
    let guess = trim !getStr
    case choose (not (guess == "")) of
        Left p => processGues (strHead' guess p)
        Right p => do
            putStrLn "Invalid input!"
            game
where
        processGuess : Char -> Eff () [MYSTERY (Running (S g) (S w)), STDIO]
                                      [MYSTERY NotRunning, STDIO]
        processGuess {g} {w} c =
            case !(Main.Guess c) of
                True => do
                    putStrLn "Good guess!"
                    case w of
                        Z => Won
                        S _ => game
                False => do
                    putStrLn "No, sorry."
                    case g of
                        Z => Lost
                        S _ => game

words : ?wtype
words = with Vect ["idris", "agda", "haskell", "miranda", "java", "javascript", "fortran",
                   "basic", "coffeescript", "rust"]

wtype = proof search

runGame : Eff () [MYSTERY NotRunning, RND, SYSTEM, STDIO]
runGame = do
    srand !time
    let w = index !(rndFin _) words
    call $ NewWord 6 w
    game
    putStrLn !(call Get)
