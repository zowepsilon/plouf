module Typer(Result, Error, State, emptyState, runProgram) where

import GHC.Data.List.SetOps
import Debug.Trace

import Ast

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

runStatement :: State -> Stmt -> Result State
runStatement state (Axiom name ty) = do
    _ <- checkExpr 0 state ty VType
    ty <- evalExpr state ty
    return $ addOpaque state name ty

runStatement state (IndDecl tyName kind constructors) = do
    _ <- checkExpr 0 state kind VType
    kindVal <- evalExpr state kind
    -- i'm not sure whether doing a readback by reusing the binding
    -- written by the user is actually sound (this is done to 
    -- improve the readability of generated induction principles)
    -- TODO: make sure it is sound
    kind <- readbackShow 0 kindVal
    kindArgs <- getKindArgs kind
    (kindArgs, state) <- evalArgList state kindArgs

    let state' = addOpaque state tyName kindVal
    (consSigs, consTypes) <- unzip <$> mapM (evalCons state') constructors

    let state'' = foldl (\state (consName, consTy) -> addOpaque state consName consTy) state' consTypes
    let ind = Inductive kindArgs consSigs

    traceShowM (inductionType tyName kindArgs consSigs)

    return $ addInductive state'' tyName ind

    where
        getKindArgs :: Expr -> Result [(String, Expr)]
        getKindArgs (Pi a t b) = do
            args <- getKindArgs b
            return $ (a, t) : args
        getKindArgs Type = return []
        getKindArgs kind = Left (NonTypeInductiveKind state kind)

        evalCons :: State -> (String, Expr) -> Result ((String, ConstructorSig), (String, Value))
        evalCons state (consName, consTy) = do
            _ <- checkExpr 0 state consTy VType
            consTyVal <- evalExpr state consTy
            consTy <- readbackShow 0 consTyVal
            (consArgs, consTyArgs) <- linearize consTy
            (consArgs, state) <- evalArgList state consArgs
            consTyArgs <- mapM (evalExpr state) consTyArgs
            return ((consName, ConsPoint consArgs consTyArgs), (consName, consTyVal))
        
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
            let state' = addOpaque state argName argTy
            (rest, state'') <- evalArgList state' rest
            return ((argName, argTy) : rest, state'')

        predicateType :: Int -> String -> [String] -> [(String, Value)]  -> (Value, Int)
        predicateType k tyName kindArgNames [] =
            let tyNameVar = NVar tyName in
            (
                VPi
                (Just "_")
                (VNeutral $ foldl
                    (\fun argName -> NApp fun $ VNeutral $ NVar argName)
                    tyNameVar
                    (reverse kindArgNames)
                )
                (\_ -> return VType),
                k
            )
        predicateType k tyName kindArgNames ((argName, argType) : rest) =
            let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k) in
            let (tail, k'') = predicateType k' tyName (var : kindArgNames) rest in
            -- isn't there a bit more bookkeeping to do if arrows are dependent?
            --                        \/ here
            (VPi (Just var) argType (\_ -> return tail), k'')
    
        consInductionArgType ::
            Int -> String -> String -> ConstructorSig 
                -> [String] -> [(String, Value)] -> (Value, Int)

        consInductionArgType k predicateName consName consSig argNames [] =
            let consNameVar = NVar consName in
            let predicateNameVar = NVar predicateName in
            let caseRet = foldl (\fun argName -> NApp fun $ VNeutral $ NVar argName) consNameVar (reverse argNames) in
            let (ConsPoint _ consKindArgs) = consSig in
            let predicateKindArgs = foldl NApp predicateNameVar consKindArgs in
            (VNeutral $ NApp predicateKindArgs $ VNeutral caseRet, k)

        consInductionArgType k predicateName consName consSig argNames ((argName, argType) : rest) =
            case argType of
                VNeutral n -> case consInductionArgTypeArgs tyName n of
                    Just argTypeArgs -> consInductionArgTypeIsInd argTypeArgs
                    _ -> consInductionArgTypeIsNotInd
                _ -> consInductionArgTypeIsNotInd

            where
                consInductionArgTypeIsInd :: [Value] -> (Value, Int)
                consInductionArgTypeIsInd argTypeArgs =
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k) in
                    let (tail, k'') = consInductionArgType k' predicateName consName consSig (var : argNames) rest in
                    let predicateNameVar = NVar predicateName in
                    let predicatePartialInstance = foldl NApp predicateNameVar argTypeArgs in
                    let predicateInstance = VNeutral $ NApp predicatePartialInstance (VNeutral $ NVar var) in
                    let tail' = VPi (Just "_") predicateInstance (\_ -> return tail) in
                    (VPi (Just var) argType (\_ -> return tail'), k'')

                consInductionArgTypeIsNotInd :: (Value, Int)
                consInductionArgTypeIsNotInd =
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k) in
                    let (tail, k'') = consInductionArgType k' predicateName consName consSig (var : argNames) rest in
                    -- same objection as in predicateType
                    (VPi (Just var) argType (\_ -> return tail), k'')
            
                consInductionArgTypeArgs :: String -> Neutral -> Maybe [Value]
                consInductionArgTypeArgs tyName (NVar f) | f == tyName = Just []
                consInductionArgTypeArgs tyName (NApp f arg) = do
                    firstArgs <- consInductionArgTypeArgs tyName f
                    return $ arg : firstArgs
                consInductionArgTypeArgs _ _ = Nothing

        inductionType :: String -> [(String, Value)] -> [(String, ConstructorSig)] -> Value
        inductionType tyName kindArgs consSigs =
            let pTy = fst $ predicateType 0 tyName [] kindArgs in
            let tail = fst $ inductionTypeCases 0 consSigs in
            -- fst $ consInductionArgType 0 tyName "P" consName firstConsSig [] consArgs
            VPi
                (Just "P")
                pTy
                (\_ -> return tail)

            where
                inductionTypeCases :: Int -> [(String, ConstructorSig)] -> (Value, Int)
                inductionTypeCases k [] =
                    inductionTypeTail k [] kindArgs

                inductionTypeCases k ((consName, consSig@(ConsPoint consArgs _)) : rest) =
                    let (tail, k') = inductionTypeCases k rest in
                    let (head, k'') = consInductionArgType k' "P" consName consSig [] consArgs in
                    (
                        VPi (Just "_") head (\_ -> return tail),
                        k''
                    )

                inductionTypeTail :: Int -> [String] -> [(String, Value)]  -> (Value, Int)
                inductionTypeTail k kindArgNames [] =
                    let var = fresh k in
                    let tyNameVar = NVar tyName in
                    let valTail = VNeutral $ foldl (\fun argName -> NApp fun $ VNeutral $ NVar argName) tyNameVar (reverse kindArgNames) in
                    let predTail = VNeutral $ foldl (\fun argName -> NApp fun $ VNeutral $ NVar argName) (NVar "P") (reverse $ var : kindArgNames) in
                    (
                        VPi
                        (Just var)
                        valTail
                        (\_ -> return predTail),
                        k+1
                    )
                inductionTypeTail k kindArgNames ((argName, argType) : rest) =
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k) in
                    let (tail, k'') = inductionTypeTail k' (var : kindArgNames) rest in
                    -- isn't there a bit more bookkeeping to do if arrows are dependent?
                    --                        \/ here
                    (VPi (Just var) argType (\_ -> return tail), k'')

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
