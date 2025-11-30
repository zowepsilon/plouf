module Typer where

import GHC.Data.List.SetOps

data Expr =
    Var String
  | Fun String Expr
  | App Expr Expr
  | Pi String Expr Expr
  | Type Integer
  deriving (Show, Eq)

data Value =
    VFun (Value -> Maybe Value)
  | VPi Value (Value -> Maybe Value)
  | VType Integer
  | VNeutral Neutral

data Neutral =
    NVar String
  | NApp Neutral Value

type Env = Assoc String Value
type TEnv = Env

evalExpr :: Env -> Expr -> Maybe Value
evalExpr env (Var x)     = assocMaybe env x
evalExpr env (Fun x e) = do
    Just $ VFun (\v -> evalExpr ((x, v) : env) e)
evalExpr _ (Type i)      = Just (VType i)
evalExpr env (App f x)   = do
    f <- evalExpr env f
    x <- evalExpr env x
    case f of
        (VFun f)   -> f x
        (VNeutral f) -> Just $ VNeutral (NApp f x)
        _            -> Nothing
evalExpr env (Pi x t e)  = do
    t <- evalExpr env t
    return $ VPi t (\v -> evalExpr ((x, v) : env) e)


fresh :: Int -> String
fresh k = "x@" ++ show k


neutral :: Int -> Neutral -> Maybe Expr
neutral _ (NVar x)   = Just $ Var x
neutral k (NApp f x) = do
    f <- neutral k f
    x <- readback k x
    return (App f x)

readback :: Int -> Value -> Maybe Expr
readback k (VFun f)     = do
    let x = fresh k
    f <- f $ VNeutral $ NVar x
    f <- readback (k+1) f
    return (Fun x f)

readback k (VPi a b)    = do
    let x = fresh k
    b <- b (VNeutral $ NVar x)
    b <- readback (k+1) b
    a <- readback k a
    return (Pi x a b)

readback _ (VType i)    = Just (Type i)
readback k (VNeutral n) = neutral k n

veq :: Int -> Value -> Value -> Bool
veq k x y = (readback k x) == (readback k y)

infer :: Int -> TEnv -> Env -> Expr -> Maybe Value
infer _ tenv _ (Var x) = assocMaybe tenv x

infer k tenv env (App fun arg) = do
    (VPi a b) <- infer k tenv env fun
    _ <- check k tenv env arg a
    arg <- evalExpr env arg
    b arg -- dependent types!!!

infer k tenv env (Pi x a b) = do
    (VType i) <- infer k tenv env a
    a <- evalExpr env a
    (VType j) <- infer k ((x, a) : tenv) env b
    return $ VType (max i j)

infer _ _ _ (Type i)  = return $ VType (i+1)
infer _ _ _ (Fun _ _) = Nothing

check :: Int -> TEnv -> Env -> Expr -> Value -> Maybe ()
check k tenv env (Fun x e) (VPi a b) = do
    let y = VNeutral (NVar (fresh k))
    b <- (b y)
    check (k+1) ((x, a) : tenv) ((x, y) : env) e b
check k tenv env e t = do
    t' <- infer k tenv env e
    if (veq k t t')
        then return ()
        else Nothing


