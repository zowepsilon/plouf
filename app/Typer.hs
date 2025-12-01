module Typer where

import GHC.Data.List.SetOps

data Expr =
    Var String
  | Fun String Expr
  | App Expr Expr
  | Pi String Expr Expr
  | Type
  deriving Eq

data Stmt =
    Declaration String (Maybe Expr) Expr
  | Axiom String Expr
  deriving Show

instance Show Expr where
    show (Var x) = x
    show (Fun x e) = "(fun " ++ x ++ " -> " ++ show e ++ ")"
    show (App f a) = "(" ++ show f ++ " " ++ show a ++ ")"

    show (Pi "_" t b) = show t ++ " -> " ++ show b ++ ")"
    show (Pi a   t b) = "(" ++ a ++ ": " ++ show t ++ ") -> " ++ show b
    
    show Type = "Type"

data Value =
    VFun (Value -> Result Value)
  | VPi Value (Value -> Result Value)
  | VType
  | VNeutral Neutral

data Neutral =
    NVar String
  | NApp Neutral Value


instance Show Value where
    show val = show $ readback 0 val

data State =
    State { env, tenv :: Assoc String Value }

instance Show State where
    show State { env=env, tenv=tenv } = showUnpacked env tenv
        where
            showUnpacked _ [] = ""
            showUnpacked env ((name, ty) : rest) =
                let cont = if null rest then "" else "\n" in
                name ++ ": " ++ show ty ++ cont ++ showUnpacked env rest

emptyState :: State
emptyState = State { env = [], tenv = [] }

addToEnv :: State -> String -> Value -> State
addToEnv state x v = state { env = (x, v) : (env state)}

addToTEnv :: State -> String -> Value -> State
addToTEnv state x v = state { tenv = (x, v) : (tenv state)}

evalExpr :: State -> Expr -> Result Value
evalExpr state (Var x)     =
    case assocMaybe (env state) x of
        Just val -> return val
        Nothing  -> Left $ UnknownVariable state x
evalExpr state (Fun x e) = do
    return $ VFun (\v -> evalExpr (addToEnv state x v) e)
evalExpr _ Type = return VType
evalExpr state (App f x)   = do
    f <- evalExpr state f
    x <- evalExpr state x
    case f of
        (VFun f)   -> f x
        (VNeutral f) -> return $ VNeutral (NApp f x)
        _            -> Left $ AppOnNonFun state f x
evalExpr state (Pi x t e)  = do
    t <- evalExpr state t
    return $ VPi t (\v -> evalExpr (addToEnv state x v) e)


fresh :: Int -> String
fresh k = "x@" ++ show k

neutral :: Int -> Neutral -> Result Expr
neutral _ (NVar x)   = return $ Var x
neutral k (NApp f x) = do
    f <- neutral k f
    x <- readback k x
    return (App f x)

readback :: Int -> Value -> Result Expr
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

readback _ VType    = return Type
readback k (VNeutral n) = neutral k n

veq :: Int -> Value -> Value -> Bool
veq k x y =
    case (readback k x, readback k y) of
        (Right e, Right e') -> e == e'
        _ -> False

inferExpr :: Int -> State -> Expr -> Result Value
inferExpr _ state (Var x) =
    case assocMaybe (tenv state) x of
        Just ty -> return ty
        Nothing -> Left $ UnknownVariableTyping state x
inferExpr k state (App fun arg) = do
    (a, b) <- case inferExpr k state fun of
        Right (VPi a b) -> return (a, b)
        Right ty -> Left $ CannotTypeAppWithoutPi state (App fun arg) ty
        Left err -> Left err
    _ <- checkExpr k state arg a
    arg <- evalExpr state arg
    b arg -- dependent types!!!

inferExpr k state (Pi x a b) = do
    case inferExpr k state a of
        Right VType -> return ()
        Right ty -> Left $ NonTypeInPiArgType state a ty
        Left err -> Left err
    a <- evalExpr state a
    let state' = addToTEnv state x a
    let y = VNeutral (NVar (fresh k))
    let state'' = addToEnv state' x y
    case inferExpr k state'' b of
        Right VType -> return ()
        Right ty -> Left $ NonTypeInPiArgType state b ty
        Left err -> Left err
    return VType

inferExpr _ _ Type = return VType
inferExpr _ state f@(Fun _ _) = Left $ CannotInferTypeOfFun state f

checkExpr :: Int -> State -> Expr -> Value -> Result ()
checkExpr k state (Fun x e) (VPi a b) = do
    let y = VNeutral (NVar (fresh k))
    b <- (b y)
    let state' = addToTEnv state x a
    let state'' = addToEnv state' x y
    checkExpr (k+1) state'' e b
checkExpr k state e t = do
    t' <- inferExpr k state e
    if (veq k t t')
        then return ()
        else Left $ MismatchedTypes state t t'

data Error =
    AppOnNonFun State Value Value
  | CannotInferTypeOfFun State Expr
  | MismatchedTypes State Value Value
  | UnknownVariable State String
  | UnknownVariableTyping State String
  | CannotTypeAppWithoutPi State Expr Value
  | NonTypeInPiArgType State Expr Value
  deriving Show

type Result a = Either Error a

runStatement :: State -> Stmt -> Result State
runStatement state (Axiom name ty) = do
    _ <- checkExpr 0 state ty VType
    ty <- evalExpr state ty
    let val = VNeutral (NVar name)
    let state' = addToEnv state name val
    return $ addToTEnv state' name ty
runStatement state (Declaration name Nothing val) = do
    ty <- inferExpr 0 state val
    runDecl state name ty val
runStatement state (Declaration name (Just ty) val) = do
    _ <- checkExpr 0 state ty VType
    ty <- evalExpr state ty
    _ <- checkExpr 0 state val ty
    runDecl state name ty val

runDecl :: State -> String -> Value -> Expr -> Result State
runDecl state name ty val = do
    val <- evalExpr state val
    let state' = addToTEnv state name ty
    let state'' = addToEnv state' name val
    return state''

runProgram :: State -> [Stmt] -> Result State
runProgram state [] = return state
runProgram state (stmt : rest) = do
    state <- runStatement state stmt
    runProgram state rest
