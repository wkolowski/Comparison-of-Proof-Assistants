import Language.Reflection.Elab
import Language.Reflection.Elab

%language ElabReflection


plusAssoc : (a : Nat) -> (b : Nat) -> (c : Nat) -> a + (b + c) = (a + b) + c
plusAssoc Z _ _ = Refl
plusAssoc (S a) b c =
    let IH = plusAssoc a b c in ?rhs
    
{-
    proof
    {
            intros
            rewrite IH
            trivial
    }
-}

