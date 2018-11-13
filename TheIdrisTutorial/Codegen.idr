module Main

%flag C "-O3"

fac : Nat -> Nat
fac Z = 1
fac (S n) = S n * fac n

fac' : Integer -> Integer
fac' 0 = 1
fac' n = n * fac' (n - 1)

main : IO ()
main = do
    printLn "Dej numerek: "
    n <- map trim getLine
    printLn $ fac' (cast n)
    pure ()