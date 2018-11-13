module Provisional

data Parity : Nat -> Type where
    Even : Parity (n + n)
    Odd : Parity (S (n + n))

-- Provisional definitions.

parity : (n : Nat) -> Parity n
parity Z = Even {n = Z}
parity (S Z) = Odd {n = Z}
parity (S (S n)) with (parity n)
    parity (S (S (k + k))) | Even ?= Even {n = S k}
    parity (S (S (S (k + k)))) | Odd ?= Odd {n = S k}

-- Suspension of disbelief.

parity' : (n : Nat) -> Parity n
parity' Z = Even {n = Z}
parity' (S Z) = Odd {n = Z}
parity' (S (S n)) with (parity n)
    parity' (S (S (k + k))) | Even = believe_me $ Even {n = S k}
    parity' (S (S (S (k + k)))) | Odd = believe_me $ Odd {n = S k}

-- Example: Binary numbers

data Binary : Nat -> Type where
    BEnd : Binary Z
    BO : Binary n -> Binary (n + n)
    BI : Binary n -> Binary (S (n + n))

natToBin : (n : Nat) -> Binary n
natToBin Z = BEnd
natToBin (S n) with (parity n)
    natToBin (S (k + k)) | Even = BI (natToBin k)
    natToBin (S (S (k + k))) | Odd ?= BO (natToBin (S k))

parity_lemma_1 = proof {
    compute;
    intros;
    rewrite sym (plusSuccRightSucc k k);
    trivial;
}

parity_lemma_2 = proof {
    compute;
    intros;
    rewrite sym (plusSuccRightSucc k k);
    trivial;
}

natToBin_lemma_1 = proof {
    compute;
    intros;
    rewrite sym (plusSuccRightSucc k k);
    trivial;
}

binToList : Binary n -> List Bool
binToList BEnd = []
binToList (BI b) = True :: binToList b
binToList (BO b) = False :: binToList b

Show (Binary n) where
    show BEnd = "0"
    show k = pack $ map (\b => if b then '1' else '0') (reverse (binToList k))

main : IO ()
main = do
    putStr "Enter a number: "
    x <- getLine
    printLn (natToBin (fromInteger (cast x)))