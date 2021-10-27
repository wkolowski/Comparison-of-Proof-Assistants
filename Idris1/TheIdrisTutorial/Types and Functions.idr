module Main

dupa : List Nat
dupa = [42, 42, 42]

mab : (a -> b) -> List a -> List b
mab f [] = []
mab f (x :: xs) = f x :: mab f xs

rev : List a -> List a
rev l = go [] l where
    go : List a -> List a -> List a
    go acc [] = acc
    go acc (x :: xs) = go (x :: acc) xs

foo : Int -> Int
foo x = case isLT of
            Yes => 2 * x
            No => 4 * x
    where
        data MyLT = Yes | No

        isLT : MyLT
        isLT = Yes

{-
even : Nat -> Bool
even Z = True
even (S k) = ?even_rhs
-}

dumb : Bool -> Type
dumb True = Nat
dumb False = List Nat

mkWut : (b : Bool) -> dumb b
mkWut True = 0
mkWut False = []

loop : Unit -> a
loop () = loop ()

codata CoNat = CZ | CS CoNat

hd : List a -> a
hd (x :: _) = x

data Vect : (n : Nat) -> (a : Type) -> Type where
    Nil : Vect Z a
    (::) : a -> Vect n a -> Vect (S n) a

(++) : Vect n a -> Vect m a -> Vect (n + m) a
--Nil ++ ys = ys
--(x :: xs) ++ ys = x :: (xs ++ ys)
(++) Nil        ys = ys
(++) (x :: xs)  ys = x :: (xs ++ ys)

data Fin : Nat -> Type where
    FZ : Fin (S n)
    FS : Fin n -> Fin (S n)

index : Fin n -> Vect n a -> a
index FZ (x :: _) = x
index (FS i) (_ :: xs) = index i xs

isEmpty : Vect n a -> Bool
isEmpty {n = Z} _ = True
isEmpty {n = S _} _ = False

{-
data IsElem : {a : Type} -> (x : a) -> Vect n a -> Type where
    Here : {xs : Vect n a} -> IsElem x (x :: xs)
    There : {y : a} -> {xs : Vect n a} -> IsElem x xs -> IsElem x (y :: xs)
-}

using (x : a, y : a, xs : Vect n a)
    data IsElem : a -> Vect n a -> Type where
        Here : IsElem x (x :: xs)
        There : IsElem x xs -> IsElem x (y :: xs)

testVect : Vect 5 Nat
testVect = [3, 4, 42, 5, 6]

inVect : IsElem 42 Main.testVect
inVect = There (There Here)

mutual
    even : Nat -> Bool
    even Z = True
    even (S n) = odd n
    
    odd : Nat -> Bool
    odd Z = False
    odd (S n) = even n

greet : IO ()
greet = do
    putStrLn "Kio estas via nomo?"
    name <- getLine
    putStrLn $ "Saluton, " ++ name ++ "!"

main : IO ()
main = do
    putStrLn "Hello, wurst!"
    greet

ifThenElse' : Bool -> Lazy a -> Lazy a -> a
ifThenElse' True x _ = x
ifThenElse' False _ x = x

infixr 10 :::

codata Strim : Type -> Type where
    (:::) : (e : a) -> Strim a -> Strim a


ones : Strim Nat
ones = 1 ::: ones

mutual
    data Blue : Type -> Type where
        B : a -> Inf (Red a) -> Blue a
    
    data Red : Type -> Type where
        R : a -> Inf (Blue a) -> Red a

mutual
    blue : Blue Nat
    blue = B 1 red

    red : Red Nat
    red = R 1 blue

mutual
    findB : (a -> Bool) -> Blue a -> a
    findB f (B x r) = if f x then x else findR f r

    findR : (a -> Bool) -> Red a -> a
    findR f (R x b) = if f x then x else findB f b

vec : (n : Nat ** Vect n Int)
vec = (_ ** [3, 4])

filter' : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter' p [] = (_ ** [])
filter' p (x :: xs) =
    let (_ ** xs') = filter' p xs in
        if p x then (_ ** x :: xs') else (_ ** xs')

filter'' : (a -> Bool) -> Vect n a -> (m ** Vect m a)
filter'' p [] = (_ ** [])
filter'' p (x :: xs) with (filter'' p xs)
    | (_ ** xs') = if p x then (_ ** x :: xs') else (_ ** xs')

data Bad : Type -> Type where
    C : (Bad a -> Bad a) -> Bad a

bad : Bad a -> a
bad b = bad b

-- Records

record Person where
    constructor MkPerson
    firstName, middleName, lastName : String
    age : Int

fred : Person
fred = MkPerson "Fred" "Joe" "Bloggs" 30

record Class where
    constructor ClassInfo

    students : Vect n Person
    className : String

addStudent : Person -> Class -> Class
addStudent p = record {students $= (p ::)}

record SizedClass (size : Nat) where
    constructor SizedClassInfo

    students : Vect size Person
    className : String

addStudent' : Person -> SizedClass n -> SizedClass (S n)
addStudent' p sc = SizedClassInfo (p :: students sc) (className sc)

-- More expressions

mirror : List a -> List a
mirror xs = let xs' = reverse xs in xs ++ xs'