import Data.Stream

%default total

myNumber : Nat
myNumber = 3

main : IO ()
main = do
  printLn "Enter your name."
  name <- getLine
  printLn $ "Hi, " ++ name ++ "!"

squareTrinomial : Double -> Double -> Double -> List Double
squareTrinomial x y z =
    let d = y * y - 4 * x * z
    in if d < 0 then []
        else if d == 0 then [(-y / 2 * x)]
            else
                let s = sqrt d
                    x1 = - y + s / 2 * x
                    x2 = - y - s / 2 * x
                in [x1, x2]

fibs : Num a => Stream a
fibs = 0 :: 1 :: zipWith (+) fibs (tail fibs)
