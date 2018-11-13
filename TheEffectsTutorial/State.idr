--import Effects

import Effects
import Effect.State

data BTree a = Empty | Node a (BTree a) (BTree a)

Functor BTree where
    map _ Empty = Empty
    map f (Node v l r) = Node (f v) (map f l) (map f r)

Show a => Show (BTree a) where
    show Empty = ""
    show (Node v l r) = "[" ++ show l ++ " " ++ show v ++ " " ++ show r ++ "]"

testTree : BTree String
testTree =
    Node "Fred"
        (Node "Jim" Empty Empty)
        (Node "Sheila"
            (Node "Alice" Empty Empty)
            (Node "Bob" Empty Empty))

t : BTree String
t = 
    Node "Fred"
        (Node "Jim" Empty Empty)
        (Node "Sheila" Empty Empty)

-- First attempt

label : BTree a -> BTree (a, Nat)
label t = Basics.fst $ aux 1 t where
    aux : Nat -> BTree a -> (BTree (a, Nat), Nat)
    aux n Empty = (Empty, n)
    aux n (Node v l r) =
        let (l', n') = aux n l in
        let (r', n'') = aux (S n') r in (Node (v, n') l' r', n'')

-- Introducing Effects

treeTagAux : BTree a -> Eff (BTree (a, Nat)) [STATE Nat]
treeTagAux Empty = pure Empty
treeTagAux (Node v l r) = do
    l' <- treeTagAux l
    n <- get
    put $ S n
    r' <- treeTagAux r
    pure $ Node (v, n) l' r'

-- This is soooo slow!
treeTag : BTree a -> BTree (a, Nat)
treeTag t = runPure (do put 1; treeTagAux t)

-- Effects and Resources

-- Labelled Effects

treeTagAux' : BTree a -> Eff (BTree (a, Nat)) ['Tag ::: STATE Nat, 'Leaves ::: STATE Nat]
treeTagAux' Empty = do
    'Leaves :- update (+1)
    pure Empty
treeTagAux' (Node v l r) = do
    l' <- treeTagAux' l
    n <- 'Tag :- get
    'Tag :- put (S n)
    r' <- treeTagAux' r
    pure $ Node (v, n) l' r'

treeTag' : BTree a -> (BTree (a, Nat), Nat)
treeTag' t = runPureInit ['Tag := 1, 'Leaves := 0]
    (do
        t' <- treeTagAux' t
        leaves <- 'Leaves :- get
        pure (t', leaves))

-- Summary:
-- ::: converts an effect to a labeled effect
-- :- converts an effectful operation to a labeled effectful operation
-- := initializes a labeled effectful operation

main : IO ()
main = do
    printLn (treeTag' testTree)

-- !-notation

stateLength : Eff Nat [STATE String]
stateLength = do
    s <- get
    pure $ length s

stateLength' : Eff Nat [STATE String]
stateLength = pure (length !get)

-- The Type Eff