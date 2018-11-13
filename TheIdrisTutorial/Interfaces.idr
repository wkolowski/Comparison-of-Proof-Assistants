module Interfaces

m_add : Maybe Int -> Maybe Int -> Maybe Int
m_add x y = do
    x' <- x
    y' <- y
    pure $ x' + y'

readNumber : IO (Maybe Nat)
readNumber = do
    input <- getLine
    if all isDigit (unpack input)
        then pure $ Just $ cast input
        else pure Nothing

readNumbers : IO (Maybe (Nat, Nat))
readNumbers = do
    Just x <- readNumber | Nothing => pure Nothing
    Just y <- readNumber | Nothing => pure Nothing
    pure $ Just (x, y)

m_add2 : Maybe Int -> Maybe Int -> Maybe Int
m_add2 x y = pure $ !x + !y

m_add3 : Maybe Int -> Maybe Int -> Maybe Int
m_add3 x y = [x' + y' | x' <- x, y' <- y]

m_add4 : Maybe Int -> Maybe Int -> Maybe Int
m_add4 x y = Just (+) <*> x <*> y

m_add5 : Maybe Int -> Maybe Int -> Maybe Int
m_add5 x y = [| x + y |]

-- An error handling interpreter.

data Expr = Var String
          | Val Int
          | Add Expr Expr

data Eval : Type -> Type where
    MkEval : (List (String, Int) -> Maybe a) -> Eval a

fetch : String -> Eval Int
fetch x = MkEval (\vars => aux vars) where
    aux : List (String, Int) -> Maybe Int
    aux [] = Nothing
    aux ((y, n) :: ys) = if x == y then Just n else aux ys

Functor Eval where
    map f (MkEval g) = MkEval (\vars => map f (g vars))

Applicative Eval where
    pure x = MkEval (\_ => Just x)
    (MkEval f) <*> (MkEval x) = MkEval (\vars => f vars <*> x vars)

eval : Expr -> Eval Int
eval (Var x) = fetch x
eval (Val n) = [| n |]
eval (Add e1 e2) = [| (+) (eval e1) (eval e2) |]

runEval : List (String, Int) -> Expr -> Maybe Int
runEval vars e =
    let MkEval f = eval e in f vars

-- Named Implementations

[gt] Ord Nat where
    compare Z Z = EQ
    compare Z (S _) = GT
    compare (S _) Z = LT
    compare (S n) (S m) = compare @{gt} n m

[SgrNatAdd] Semigroup Nat where
    (<+>) = (+)

[SgrNatMul] Semigroup Nat where
    (<+>) = (*)

[MonNatAdd] Monoid Nat using SgrNatAdd where
    neutral = 0

[MonNatMul] Monoid Nat using SgrNatMul where
    neutral = 1