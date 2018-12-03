import Language.Reflection.Elab
import Language.Reflection.Elab

%language ElabReflection

-- The Interactive Theorem Prover

plusAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + (b + c) = (a + b) + c
plusAssoc Z _ _ = Refl
plusAssoc (S a) b c = rewrite plusAssoc a b c in Refl

{-
    proof
    {
            intros
            rewrite IH
            trivial
    }
-}

plusAssoc' : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + (b + c) = (a + b) + c
plusAssoc' a b c = ?a