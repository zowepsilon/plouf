module Typer(Result, Error, State, emptyState, runProgram) where

import GHC.Data.List.SetOps
import Debug.Trace

import Ast

data Value =
    VFun (Maybe String) (Value -> Result Value)
  | VPi (Maybe String) Value (Value -> Result Value)
  | VType
  | Vind String Value [Value]
  | VNeutral Neutral

data Neutral =
    NVar String
  | NApp Neutral Value

instance Show Value where
    show val = case readbackShow 0 val of
        Right repr -> show repr
        Left err -> "{error in readback: " ++ show err ++ "}"

        where
            neutralShow _ (NVar x)   = return $ Var x
            neutralShow k (NApp f x) = do
                f <- neutralShow k f
                x <- readbackShow k x
                return (App f x)

            readbackShow k (VFun displayName f) = do
                let (x, k') = var displayName k
                f <- f $ VNeutral $ NVar x
                f <- readbackShow k' f
                return (Fun x f)

            readbackShow k (VPi displayName a b) = do
                let (x, k') = var displayName k
                b <- b (VNeutral $ NVar x)
                b <- readbackShow k' b
                a <- readbackShow k a
                return (Pi x a b)

            readbackShow _ VType    = return Type
            readbackShow k (VNeutral n) = neutralShow k n
 
            var (Just name) k = (name, k)
            var (Nothing)   k = (fresh k, k+1)

data ConstructorSig = ConsPoint [(String, Value)] [Value]
    deriving Show

data Inductive = Inductive [(String, Value)] (Assoc String ConstructorSig)
    deriving Show

data State = State { env, tenv :: Assoc String Value, indTypes :: Assoc String Inductive }

instance Show State where
    show State { env=env, tenv=tenv } = showUnpacked env (reverse tenv)
        where
            showUnpacked :: [(String, Value)] -> [(String, Value)] -> String
            showUnpacked _ [] = ""
            showUnpacked env ((name, ty) : rest) =
                let cont = if null rest then "" else "\n" in
                name ++ ": " ++ show ty ++ cont ++ showUnpacked env rest

emptyState :: State
emptyState = State { env = [], tenv = [], indTypes = [] }

addToEnv :: State -> String -> Value -> State
addToEnv state x v = state { env = (x, v) : (env state)}

addToTEnv :: State -> String -> Value -> State
addToTEnv state x v = state { tenv = (x, v) : (tenv state)}

addOpaque :: State -> String -> Value -> State
addOpaque state name ty =
    let val = VNeutral (NVar name) in
    let state' = addToEnv state name val in
    addToTEnv state' name ty

addInductive :: State -> String -> Inductive -> State
addInductive state name ind = state { indTypes = (name, ind) : (indTypes state) }

evalExpr :: State -> Expr -> Result Value
evalExpr state (Var x)     =
    case assocMaybe (env state) x of
        Just val -> return val
        Nothing  -> Left $ UnknownVariable state x
evalExpr state (Fun x e) = do
    return $ VFun (Just x) (\v -> evalExpr (addToEnv state x v) e)
evalExpr _ Type = return VType
evalExpr state (App f x)   = do
    f <- evalExpr state f
    x <- evalExpr state x
    case f of
        (VFun _ f)   -> f x
        (VNeutral f) -> return $ VNeutral (NApp f x)
        _            -> Left $ AppOnNonFun state f x
evalExpr state (Pi x t e)  = do
    t <- evalExpr state t
    return $ VPi (Just x) t (\v -> evalExpr (addToEnv state x v) e)


fresh :: Int -> String
fresh k = "?" ++ show k

neutral :: Int -> Neutral -> Result Expr
neutral _ (NVar x)   = return $ Var x
neutral k (NApp f x) = do
    f <- neutral k f
    x <- readback k x
    return (App f x)

readback :: Int -> Value -> Result Expr
readback k (VFun _ f)     = do
    let x = fresh k
    f <- f $ VNeutral $ NVar x
    f <- readback (k+1) f
    return (Fun x f)

readback k (VPi _ a b)    = do
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
        Right (VPi _ a b) -> return (a, b)
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
checkExpr k state (Fun x e) (VPi _ a b) = do
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
  | NonTypeInductiveKind State Expr
  | InvalidConstructorType State Expr
  deriving Show

type Result a = Either Error a

runStatement :: State -> Stmt -> Result State
runStatement state (Axiom name ty) = do
    _ <- checkExpr 0 state ty VType
    ty <- evalExpr state ty
    return $ addOpaque state name ty

runStatement state (IndDecl tyName kind constructors) = do
    _ <- checkExpr 0 state kind VType
    kindVal <- evalExpr state kind
    kind <- readback 0 kindVal
    kindArgs <- getKindArgs kind
    (kindArgs, state) <- evalArgList state kindArgs
    let ty = VNeutral (NVar tyName)
    let state' = addOpaque state tyName kindVal
    (consSigs, consTypes) <- unzip <$> mapM (evalCons state' tyName) constructors
    let state'' = foldl (\state (consName, consTy) -> addOpaque state consName consTy) state' consTypes
    let ind = Inductive kindArgs consSigs
    -- TODO: add constructors to the value & typing scopes
    traceShow ind (return ())
    return $ addInductive state'' tyName ind
    where
        getKindArgs :: Expr -> Result [(String, Expr)]
        getKindArgs (Pi a t b) = do
            args <- getKindArgs b
            return $ (a, t) : args
        getKindArgs Type = return []
        getKindArgs kind = Left (NonTypeInductiveKind state kind)

        evalCons :: State -> String -> (String, Expr) -> Result ((String, ConstructorSig), (String, Value))
        evalCons state tyName (consName, consTy) = do
            _ <- checkExpr 0 state consTy VType
            consTyVal <- evalExpr state consTy
            consTy <- readback 0 consTyVal
            (consArgs, consTyArgs) <- linearize consTy
            (consArgs, state) <- evalArgList state consArgs
            consTyArgs <- mapM (evalExpr state) consTyArgs
            return ((tyName, ConsPoint consArgs consTyArgs), (consName, consTyVal))
        
        linearize :: Expr -> Result ([(String, Expr)], [Expr])
        linearize (Pi a t b) = do
            (args, tail) <- linearize b
            return ((a, t) : args, tail)
        linearize consTy = do
            tail <- linearizeTail tyName consTy
            return $ ([], tail)

        linearizeTail :: String -> Expr -> Result [Expr]
        linearizeTail tyName (Var x) | x == tyName = return []
        linearizeTail tyName (App f arg) = do
            tail <- linearizeTail tyName f 
            return (arg : tail)
        linearizeTail _ ret = Left $ InvalidConstructorType state ret

        evalArgList :: State -> [(String, Expr)] -> Result ([(String, Value)], State)
        evalArgList state [] = return ([], state)
        evalArgList state ((argName, argTy) : rest) = do
            argTy <- evalExpr state argTy
            let state' = addToEnv state argName argTy
            (rest, state'') <- evalArgList state' rest
            return ((argName, argTy) : rest, state'')
        

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
