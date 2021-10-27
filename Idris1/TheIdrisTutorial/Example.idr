module Example

import Data.Vect
import Data.Fin

-- Representing Languages

data Ty = TyInt | TyBool | TyFun Ty Ty

interpTy : Ty -> Type
interpTy TyInt = Integer
interpTy TyBool = Bool
interpTy (TyFun a b) = interpTy a -> interpTy b

using (G : Vect n Ty)

    data HasType : (i : Fin n) -> Vect n Ty -> Ty -> Type where
        Stop : HasType FZ (t :: G) t
        Pop : HasType k G t -> HasType (FS k) (u :: G) t

    data Expr : Vect n Ty -> Ty -> Type where
        Var : HasType i G t -> Expr G t
        Val : (x : Integer) -> Expr G TyInt
        Lam : Expr (t1 :: G) t2 -> Expr G (TyFun t1 t2)
        App : Expr G (TyFun t1 t2) -> Expr G t1 -> Expr G t2
        Op : (interpTy a -> interpTy b -> interpTy c) ->
                Expr G a -> Expr G b -> Expr G c
        If : Expr G TyBool -> Lazy (Expr G t) -> Lazy (Expr G t) -> Expr G t

-- Writing the interpreter.

    data Env : Vect n Ty -> Type where
        Nil : Env Nil
        (::) : interpTy a -> Env G -> Env (a :: G)

    lookup : HasType i G t -> Env G -> interpTy t
    lookup Stop (x :: _) = x
    lookup (Pop ht) (_ :: xs) = lookup ht xs

    interp : Env G -> Expr G t -> interpTy t
    interp env (Var ht) = lookup ht env
    interp _ (Val n) = n
    interp env (Lam e) = \x => interp (x :: env) e
    interp env (App e1 e2) = (interp env e1) (interp env e2)
    interp env (Op f a b) = f (interp env a) (interp env b)
    interp env (If cond e1 e2) =
        if interp env cond then interp env e1 else interp env e2

    add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
    add = Lam (Lam (Op (+) (Var Stop) (Var (Pop Stop))))

    fact : Expr G (TyFun TyInt TyInt)
    fact = Lam (If (Op (==) (Var Stop) (Val 0))
                   (Val 1)
                   (Op (*) (Var Stop) (App fact (Op (-) (Var Stop) (Val 1)))))

-- dsl notation, but doesn't work
{-
    mkLam : TTName -> Expr (t1 :: g) t2 -> Expr g (TyFun t1 t2)
    mkLam _ body = Lam body

    dsl expr
        variable = Var
        index_first = Stop
        index_next = Pop
        lambda = mkLam

    fact : Expr G (TyFun Int Int)
    fact = expr (\x => If (Op (==) x (Val 0))
                        (Val 1)
                        (Op (*) x (App fact (Op (-) x (Val 1)))))

    (<*>) : (f : Lazy (Expr G (TyFun t1 t2))) -> Expr G t1 -> Expr G t2
    (<*>) f a = App f a

    pure : Expr G a -> Expr G a
    pure = id

    fact' : Expr G (TyFun Int Int)
    fact' = expr (\x => If (Op (==) x (Val 0))
                        (Val 1)
                        (Op (*) x [| fact (Op (-) x (Val 1))))

    syntax "IF" [x] "THEN" [e1] "ELSE" [e2] = If x e1 e2
-}

    main : IO ()
    main = do
        putStr "Enter a number: "
        n <- getLine
        printLn $ interp [] fact (cast n)