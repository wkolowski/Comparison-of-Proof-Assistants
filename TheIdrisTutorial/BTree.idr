module BTree

--data BTree a = Empty | Node a (BTree a) (BTree a)

%access export

public export
data BTree : Type -> Type where
    Empty : BTree a
    Node : a -> BTree a -> BTree a -> BTree a

insert : Ord a => a -> BTree a -> BTree a
insert x Empty = Node x Empty Empty
insert x t@(Node v l r) =
    case compare x v of
        LT => Node v (insert x l) r
        EQ => t
        GT => Node v l (insert x r)

toList : BTree a -> List a
toList Empty = []
toList (Node v l r) = toList l ++ v :: toList r

toTree : Ord a => List a -> BTree a
toTree [] = Empty
toTree (x :: xs) = insert x (toTree xs)