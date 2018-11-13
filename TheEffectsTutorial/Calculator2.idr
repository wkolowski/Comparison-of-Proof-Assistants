-- Console I/O

import Data.Vect

import Effects
import Effect.State
import Effect.Exception
import Effect.Random
import Effect.System

data Expr
    = Var String
    | Val Integer
    | Add Expr Expr
    | Random Integer Integer

Env : Type
Env = List (String, Integer)

EvalEff : Type -> Type
--EvalEff t = Eff t [EXCEPTION String, STATE Env, RND]
EvalEff t = Eff t [EXCEPTION String, STATE Env, RND, SYSTEM]

eval : Expr -> EvalEff Integer
eval (Val k) = pure k
eval (Var v) = do
    case lookup v !get of
        Nothing => raise $ "Variable " ++ v ++ " is undefined"
        Just k => pure k
eval (Add e1 e2) = [| (+) (eval e1) (eval e2) |]
eval (Random a b) = rndInt a b

--runEval : Env -> Expr -> Maybe Integer
runEval : Env -> Expr -> IO Integer
runEval env e = run (eval' e) where
    eval' : Expr -> EvalEff Integer
    eval' e = do
        srand !time
        put env
        eval e