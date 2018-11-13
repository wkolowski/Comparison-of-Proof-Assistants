module Interactive

import Data.Vect

-- Editing at the REPL

-- :command [line number] [name]
-- :command! [line number] [name]

-- Editing Commands

vzipWith : (a -> b -> c) -> Vect n a -> Vect n b -> Vect n c
vzipWith f [] [] = []
vzipWith f (x :: xs) (y :: ys) = f x y :: vzipWith f xs ys
