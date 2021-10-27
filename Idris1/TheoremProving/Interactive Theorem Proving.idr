nat_ind : (P : Nat -> Type) -> P Z -> ((n : Nat) -> P n -> P (S n)) -> (n : Nat) -> P n
nat_ind P hz _ Z = hz
nat_ind P hz hs (S n) = hs n (nat_ind P hz hs n)

-- DEPRECATED: Interactive Theorem Proving

plus_n_Z : (n : Nat) -> n + 0 = n
plus_n_Z Z = Refl
plus_n_Z (S n) = rewrite plus_n_Z n in Refl

plus_n_Z' : (n : Nat) -> n + 0 = n
plus_n_Z' Z = Refl {- proof
    refine Refl
    Sadly, this is deprecated-}
plus_n_Z' (S n) = ?b

plus_n_Z'' : (n : Nat) -> n + 0 = n
plus_n_Z'' = ?c