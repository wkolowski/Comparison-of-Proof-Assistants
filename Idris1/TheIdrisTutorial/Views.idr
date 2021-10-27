module Views

import Data.Vect

filter1 : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter1 _ [] = (_ ** [])
filter1 p (x :: xs) with (filter1 p xs)
    filter1 p (x :: xs) | (_ ** xs') =
        if p x then (_ ** x :: xs') else (_ ** xs')

filter2 : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter2 _ [] = (_ ** [])
filter2 p (x :: xs) with (filter2 p xs)
    | (_ ** xs') = if p x then (_ ** x :: xs') else (_ ** xs')

foo : Int -> Int -> Bool
foo n m with (succ n)
    foo _ m | 2 with (succ m)
        foo _ _ | 2 | 3 = True
        foo _ _ | 2 | _ = False
    foo _ _ | _ = False

data Parity : Nat -> Type where
    Even : Parity (n + n)
    Odd : Parity (S (n + n))

helpEven : (n : Nat) -> Parity (S n + S n) -> Parity (S (S (n + n)))
helpEven n p = rewrite plusSuccRightSucc n n in p

helpOdd : (n : Nat) -> Parity (S (S n + S n)) -> Parity (S (S (S (n + n))))
helpOdd n p = rewrite plusSuccRightSucc n n in p

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S n)) with (parity n)
    parity (S (S (k + k))) | Even =
        let result = Even {n = S k} in helpEven k result
    parity (S (S (S (k + k)))) | Odd =
        let result = Odd {n = S k} in helpOdd k result

natToBin : Nat -> List Bool
natToBin Z = []
natToBin n with (parity n)
    natToBin (k + k) | Even = False :: natToBin k
    natToBin (S (k + k)) | Odd = True :: natToBin k 

-- With and proofs

data Foo = FInt Int | FBool Bool

optional : Foo -> Maybe Int
optional (FInt x) = Just x
optional (FBool _) = Nothing

isFInt : (foo : Foo) -> Maybe (x : Int ** (optional foo = Just x))
isFInt foo with (optional foo) proof p
    isFInt foo | Nothing = Nothing
    isFInt foo | (Just x) = Just (x ** Refl)