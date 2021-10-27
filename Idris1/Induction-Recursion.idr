mutual
  data U : Type where
    Top : U
    Bot : U
    Sum : (t : U) -> (inj t -> U) -> U
    Prod : (t : U) -> (inj t -> U) -> U

  inj : U -> Type
  inj Top = ()
  inj Bot = Void
  inj (Sum c x) =  (v : inj c ** inj (x v))
  inj (Prod c x) = (v : inj c) -> inj (x v)