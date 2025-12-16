module Ast where

import Data.List
import GHC.Data.List.SetOps

data Expr =
    Var String
  | Fun String Expr
  | App Expr Expr
  | Pi String Bool Expr Expr
  | Type
  | Ind String [Expr] -- constructed only through readback for type checking
  | By [TacticStmt]
  deriving Eq

data TacticStmt =
    TacIntro [String]
  | TacUse Expr
  | TacInduction
  deriving (Show, Eq)

data Stmt =
    Declaration String (Maybe Expr) Expr
  | Axiom String Expr
  | IndDecl String Expr [(String, Expr)]
  | Print Expr
  deriving Show

data Value =
    VFun (Maybe String) (Value -> Result Value)
  | VPi (Maybe String) Bool Value (Value -> Result Value)
  | VType
  --     induction type name
  --            branches
  | VInd String [Value]
  | VNeutral Neutral

data Neutral =
    NVar String
  | NApp Neutral Value
  | NIndApp String [Value] Neutral
  deriving Show

data ConstructorSig = ConsPoint [(String, Value)] [Bool] [Value]
    deriving Show

data Inductive = Inductive [(String, Value)] (Assoc String ConstructorSig)
    deriving Show

data State = State {
        env, tenv :: Assoc String Value,
        indTypes :: Assoc String Inductive
    }

data Error
    = AppOnNonFun State Value Value
    | CannotInferTypeOfFun State Expr
    | CannotInferTypeOfBy State Expr
    | MismatchedTypes State Value Value
    | UnknownVariable State String
    | UnknownVariableTyping State String
    | CannotTypeAppWithoutPi State Expr Value
    | NonTypeInPiArgType State Expr Value
    | NonTypeInductiveKind State Expr
    | InvalidConstructorType State Expr
    | Unreachable State String
    | UnknownInductiveType State String
    | RecursorArgumentIsNotAConstructor State Value
    | UnknownConstructorForInductive State String Inductive
    | UnexpectedTacticForTy State TacticStmt Value
    | UnfilledHole State Value
    | RemainingTactics State [TacticStmt]
    | IncorrectlyBuiltExpression [TacticStmt] Error
    | IntroTacticOnNonPi State TacticStmt String Value
    | MismatchedTypesInUseTactic State Value Value
    | UnificationFailure Expr Expr
    | UnconstraintedImplicitArg String Expr [Result Expr] [Expr]
    | CannotUseInductionTactic State Value
    deriving Show

type Result a = Either Error a

instance Show Expr where
    show (Var x) = x
    show e@(Fun _ _) =
        let (args, body) = showFun e in
        "(fun " ++ (intercalate " " args) ++ " -> " ++ show body ++ ")"
        where
            showFun (Fun x e) =
                let (args, body) = showFun e in
                (x : args, body)
            showFun e = ([], e)

    show (App f a) = "(" ++ showApp f [a] ++ ")"
        where
            showApp (App f a) tail = showApp f (a : tail)
            showApp fun args = show fun ++ " " ++ intercalate " " (map show args)

    show (Pi "_" False t@(Fun _ _) b) = "(" ++ show t ++ ") -> " ++ show b
    show (Pi "_" True  t@(Fun _ _) b) = "{" ++ show t ++ "} -> " ++ show b

    show (Pi "_" False t@(Pi _ _ _ _) b) = "(" ++ show t ++ ") -> " ++ show b
    show (Pi "_" True  t@(Pi _ _ _ _) b) = "{" ++ show t ++ "} -> " ++ show b

    show (Pi "_" _ t b) = show t ++ " -> " ++ show b

    show (Pi a False t b) = "(" ++ a ++ ": " ++ show t ++ ") -> " ++ show b
    show (Pi a True  t b) = "{" ++ a ++ ": " ++ show t ++ "} -> " ++ show b
    
    show (Ind tyName args) =
        tyName ++ ".ind " ++ intercalate " " (map show args)

    show (By stmts) = "by  \n    " ++ intercalate "\n    " (map show stmts)

    show Type = "Type"

instance Show Value where
    show val = case readbackShow 0 val of
        Right repr -> show repr
        Left err -> "{error in readbackShow: " ++ show err ++ "}"


readbackShow :: Int -> Value -> Result Expr
neutralShow :: Int -> Neutral -> Result Expr 

neutralShow _ (NVar x)   = return $ Var x
neutralShow k (NApp f x) = do
    f <- neutralShow k f
    x <- readbackShow k x
    return (App f x)
neutralShow k (NIndApp tyName branches x) = do
    branches <- mapM (readbackShow k) branches
    x <- neutralShow k x
    return $ App (Ind tyName branches) x

readbackShow k (VFun displayName f) = do
    let (x, k') = var displayName k
    f <- f $ VNeutral $ NVar x
    f <- readbackShow k' f
    return (Fun x f)
    where
        var (Just name) k = (name, k)
        var (Nothing)   k = (fresh k, k+1)

readbackShow k (VPi displayName implicit a b) = do
    let (x, k') = var displayName k
    b <- b (VNeutral $ NVar x)
    b <- readbackShow k' b
    a <- readbackShow k a
    return (Pi x implicit a b)
    where
        var (Just name) k = (name, k)
        var (Nothing)   k = (fresh k, k+1)

readbackShow k (VInd tyName args) = do
    args <- mapM (readbackShow k) args
    return (Ind tyName args)

readbackShow _ VType    = return Type
readbackShow k (VNeutral n) = neutralShow k n


instance Show State where
    show State { env=env, tenv=tenv } = "\n" ++ showUnpacked env (reverse tenv) ++ "\n"
        where
            showUnpacked :: [(String, Value)] -> [(String, Value)] -> String
            showUnpacked _ [] = ""
            showUnpacked env ((name, ty) : rest) =
                let cont = if null rest then "" else "\n" in
                name ++ ": " ++ show ty ++ cont ++ showUnpacked env rest

emptyState :: State
emptyState = State { env = [], tenv = [], indTypes = [] }

addToEnv :: State -> String -> Value -> State
addToEnv state "_" _ = state
addToEnv state x v = state { env = (x, v) : (env state)}

addToTEnv :: State -> String -> Value -> State
addToTEnv state "_" _ = state
addToTEnv state x v = state { tenv = (x, v) : (tenv state)}

addOpaque :: State -> String -> Value -> State
addOpaque state name ty =
    let val = VNeutral (NVar name) in
    let state' = addToEnv state name val in
    addToTEnv state' name ty

addInductive :: State -> String -> Inductive -> State
addInductive state name ind = state { indTypes = (name, ind) : (indTypes state) }

fresh :: Int -> String
fresh k = "&" ++ show k
