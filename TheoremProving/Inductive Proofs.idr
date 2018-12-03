-- Inductive Proofs

nat_ind : (P : Nat -> Type) -> P Z -> ((n : Nat) -> P n -> P (S n)) -> (n : Nat) -> P n
nat_ind P hz _ Z = hz
nat_ind P hz hs (S n) = hs n (nat_ind P hz hs n)

plus_ind : Nat -> Nat -> Nat
plus_ind n m =
    nat_ind (\_ => Nat) m (\_, r => S r) n