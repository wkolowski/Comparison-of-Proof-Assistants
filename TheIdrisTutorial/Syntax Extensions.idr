import Data.So

-- syntax rules

-- It's important to put the new syntax fragments in quotes.
syntax "jeszli" [test] "to" [e1] "a jak nie to" [e2] = ifThenElse test e1 e2

data Interval : Type where
    MkInterval : (lower : Double) -> (upper : Double) -> So (lower < upper) -> Interval

pattern syntax "[" [x] "..." [y] "]" = MkInterval x y Oh
term    syntax  "[" [x] "..." [y] "]" = MkInterval x y ?bound_lemma

wut : Nat
wut = 42

forM : Monad m => List a -> (a -> m b) -> m (List b)
forM [] _ = pure []
forM (x :: xs) f = do
    h <- f x
    t <- forM xs f
    pure $ h :: t

syntax for {x} "in" [xs] ":" [body] = forM xs (\x => body)

main : IO ()
main = do
    for x in [1..10]:
        printLn x
    pure ()