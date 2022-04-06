import Data.List
import Data.List.Elem
import Data.List.Elem.Extra

elemInRev : (xs : List a) -> x `Elem` xs -> x `Elem` (reverse xs)
elemInRev (x :: xs) Here =
  let --p1 : x `Elem` (reverse xs ++ [x])
      p1 := elemAppRight (reverse xs) [x] Here
      p2 : (reverse xs ++ [x] = reverse (x :: xs))
      p2 = revAppend [x] xs
  in replace {p=(\y => x `Elem` y)} p2 p1 --rewrite (sym p2) in ?hole

elemInRev (y :: xs) (There pos) =
  let p = elemInRev xs pos
      p2 : (reverse xs ++ [y] = reverse (y :: xs))
  in rewrite (sym p2) in elemAppLeft _ _ p
