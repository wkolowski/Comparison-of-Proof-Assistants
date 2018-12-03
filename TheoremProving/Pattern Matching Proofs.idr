-- Pattern Matching Proofs

pluz : Nat -> Nat -> Nat
pluz Z m = m
pluz (S n) m = S (pluz n m)

-- Creating a definition

-- Base Case
total
pluz_comm_Z : (m : Nat) -> m = pluz m Z
pluz_comm_Z Z = Refl
pluz_comm_Z (S m) = rewrite (pluz_comm_Z m) in Refl

-- Inductive Step
total
pluz_comm_S : (n, m : Nat) -> S (pluz n m) = pluz n (S m)
pluz_comm_S Z m = Refl
pluz_comm_S (S n) m = rewrite pluz_comm_S n m in Refl

total
pluz_comm : (n, m : Nat) -> pluz n m = pluz m n
pluz_comm Z m = pluz_comm_Z m
pluz_comm (S n) m =
    rewrite pluz_comm n m in
        rewrite pluz_comm_S m n in Refl

total
pluzC : (n, m : Nat) -> pluz n m = pluz m n
pluzC Z Z = Refl
pluzC Z (S m) = rewrite pluzC Z m in Refl
pluzC (S n) Z = rewrite pluzC n Z in Refl
pluzC (S n) (S m) =
    rewrite sym (pluzC (S n) m) in
        rewrite pluzC n (S m) in
            rewrite pluzC n m in Refl