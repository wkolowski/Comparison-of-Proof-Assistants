||| Replicate constr...
rep : Nat -> a -> List a

--rep 0 x = []
--rep (S k) x = ?rep_rhs_2

uncurry : (a -> b -> c) -> (a, b) -> c
uncurry f x = ?uncurry_rhs

--uncurry f (x, y) = f x y

-- rep Z     e = []
-- rep (S k) e = e :: rep k e

-- %hide Nat
-- data Nat : Type where
--   Z : Nat
--   S : Nat -> Nat

-- %hide Nat
-- data Nat = Z | S Nat
--

-- dependent function
0 myType : Nat -> Type
myType Z = Bool
myType (S k) = Nat

f : (n : Nat) -> myType n -> Type
-- f Z     = True
-- f (S k) = S k

g : f n m
g = ?g_rhs

--vector
data Vect : Nat -> Type -> Type where
  Nil   : Vect Z a
  (::)  : a -> Vect n a -> Vect (S n) a

0 j : Vect n a -> Nat
j x = n

takeHead : Vect 1 Nat -> Nat
takeHead (x :: []) = x


0 typeOf : (_ : a) -> Type
typeOf _ = a

-- dependent pair
%hide DPair
record DPair' (a : Type) (p : a -> Type) where
    constructor MkDPair'
    0 fs : a
    sn : p fs

-- data DPair : (a : Type) -> (p : a -> Type) -> Type where
--    MkDPair : {p : a -> Type} -> (0 x : a) -> p x -> DPair a p
--
-- (.fst) : DPair a p -> a
-- (MkDPair x y).fst = x
--
-- (.snd) : (d: DPair a p) -> p d.fst
-- (MkDPair x y).snd = y

dodo : DPair' Nat (\x => x = 0)
dodo = MkDPair' Z Refl

-- l : (dodo .fs = 0)
-- l = sn dodo

n : (dodo : DPair' Nat (\x => x = 0)) -> (dodo .fs = 0)
n dodo' =
  let --dodo : DPair' Nat (\x => x = 0)
      u : Nat
      u = 0
      dodo := 1
      -- l : (dodo .fs = 0)
      -- l = sn dodo
  in ?l


k : Type -> Int
k Int = ?k_rhs
k Nat = ?k_rhs2
k _ = ?k_rhs3

-- -- runtime irrelevant
-- head : (xs : List a)
--      -> {0 y : a}
--      -> {0 ys : List a}
--      -> (0 prf : xs = (y::ys))
--      -> a
-- head (y :: _) Refl = y

-- auto
head : (xs : List a)
     -> {0 y : a}
     -> {0 ys : List a}
     -> {auto 0 prf : [] = (y::ys)}
     -> a
head (_ :: _) impossible

-- ordering
max' : Ord a => a -> a -> a
max' x y = if x > y then x else y

data Levels = One | Two | Three

Eq Levels where
  (One == One) = True
  (Two == Two) = True
  (Three == Three) = True
  _ == _ = False

Ord Levels where
  compare One x =  LT
  compare Two One =  LT
  compare Two Two =  EQ
  compare Two Three = GT
  compare Three x =  GT

-- search
-- uncurry : (a -> b -> c) -> (a, b) -> c

-- append : (1 _ : List a) -> (1 _ : List a) -> List a
-- append [] ys = ys
-- append (x :: xs) ys = x :: append xs ys
