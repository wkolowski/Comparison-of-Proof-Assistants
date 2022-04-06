import Data.List.Elem


infix 3 <->
||| If and only if relation between predicates
record (<->) {a : Type} (p, q : a -> Type) where
  constructor And
  If     : (x : a) -> (q x -> p x)
  onlyIf : (x : a) -> (p x -> q x)


data Reflects : (p : a -> Type) -> (Maybe a) -> Type where
  Indeed    : {0 p : a -> Type}
            -> (prf : p x)
            -> Reflects p (Just x)
  Otherwise : {0 p : a -> Type}
            -> (prf : (x : a) -> Not (p x))
            -> Reflects p Nothing

record RMaybe {a : Type} (p : a -> Type) where
  constructor Because
  Holds   : Maybe a
  0 Proof : Reflects p Holds


map : {0 p,q : a -> Type} -> p <-> q -> RMaybe p -> RMaybe q

h : {pred : a -> Bool} -> (x : a) -> (Elem x [], pred x = True) -> Void
h _ (Here, _) impossible
h _ (There y, _) impossible

findR : {0 a : Type} -> (pred : a -> Bool) -> (xs : List a)
      -> RMaybe (\x => (x `Elem` xs, pred x = True))
findR pred [] = Nothing `Because` Otherwise (\_ => \case (_, _) impossible)
findR pred (x :: xs) with (pred x) proof p
  findR pred (x :: xs) | False =
    let (Because q r) := findR pred xs
    in
      case q of
        Nothing =>
          Because Nothing (case r of
            Otherwise h =>
              Otherwise (\y , (z, w) => case z of
                Here => absurd $ trans (sym p) w
                There i => h y (i, w)))
        Just y => Because (Just y) (Indeed (case r of
          Indeed (h, i) => (There h, i)))
  findR pred (x :: xs) | True = Just x `Because` Indeed (Here, p)
