import Effects

data State : Effect where
    Get : State a a (\x => a)
    Put : b -> State () a (\x => b)

STATE : Type -> EFFECT
STATE t = MkEff t State

Handler State m where
    handle s Get k = k s s
    handle _ (Put s') k = k () s'

get : Eff s [STATE s]
get = call Get

put : a -> Eff () [STATE a]
put s = call (Put s)

putM : b -> Eff () [STATE a] [STATE b]
putM s = call (Put s)

-- Let's see if this is really the same as the STATE from the standard library.

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

main : IO ()
main = do
    printLn (treeTag testTree)
