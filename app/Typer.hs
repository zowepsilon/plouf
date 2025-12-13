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
        (VInd tyName branches) -> undefined
        _            -> Left $ AppOnNonFun state f x
evalExpr state (Pi x t e)  = do
    t <- evalExpr state t
    return $ VPi (Just x) t (\v -> evalExpr (addToEnv state x v) e)

evalExpr state e@(Ind _ _) = Left $ Unreachable state ("tried to evalExpr " ++ show e)

neutral :: Int -> Neutral -> Result Expr
neutral _ (NVar x)   = return $ Var x
neutral k (NApp f x) = do
    f <- neutral k f
    x <- readback k x
    return (App f x)

readback :: Int -> Value -> Result Expr
readback k (VFun _ f) = do
    let x = fresh k
    f <- f $ VNeutral $ NVar x
    f <- readback (k+1) f
    return (Fun x f)

readback k (VPi _ a b) = do
    let x = fresh k
    b <- b (VNeutral $ NVar x)
    b <- readback (k+1) b
    a <- readback k a
    return (Pi x a b)

readback _ VType = return Type

readback k (VInd tyName args) = do
    args <- mapM (readback k) args
    return (Ind tyName args)

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
inferExpr _ state e@(Ind _ _) = Left $ Unreachable state ("tried to inferExpr " ++ show e)

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
    (kindArgsVal, state) <- evalArgList state kindArgs
    kindArgs <- mapM (\(name, val) -> do
            val <- readbackShow 0 val
            return (name, val)
        ) kindArgsVal

    let state' = addOpaque state tyName kindVal
    (consSigs, consTypes) <- unzip <$> mapM (evalCons state') constructors
    (consTypesVal, state') <- evalArgList state' consTypes

    let state'' = foldl (\state (consName, consTy) -> addOpaque state consName consTy) state' consTypesVal

    -- TODO: precompute how to recurse
    let ind = Inductive kindArgsVal consSigs
    traceShowM ind
    
    let indName = (tyName ++ ".ind")
    -- predicate + cases + type arguments for value
    let indArity = 1 + length kindArgs + length consSigs
    let state''' = addInductive state'' tyName ind
    indTy <- inductionType tyName kindArgs consSigs
    indTy <- evalExpr state''' indTy
    let state'''' = addToTEnv state''' indName indTy
    let state''''' = addToEnv state'''' indName (inductionClosure tyName indArity)

    return state'''''

    where
        getKindArgs :: Expr -> Result [(String, Expr)]
        getKindArgs (Pi a t b) = do
            args <- getKindArgs b
            return $ (a, t) : args
        getKindArgs Type = return []
        getKindArgs kind = Left (NonTypeInductiveKind state kind)

        evalCons :: State -> (String, Expr) -> Result ((String, ConstructorSig), (String, Expr))
        evalCons state (consName, consTy) = do
            _ <- checkExpr 0 state consTy VType
            consTyVal <- evalExpr state consTy
            consTy <- readbackShow 0 consTyVal
            (consArgs, consTyArgs) <- linearize consTy
            (consArgs, state) <- evalArgList state consArgs
            consTyArgs <- mapM (evalExpr state) consTyArgs
            return ((consName, ConsPoint consArgs consTyArgs), (consName, consTy))
        
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

        predicateType :: Int -> String -> [String] -> [(String, Expr)]  -> (Expr, Int)
        predicateType k tyName kindArgNames [] =
            let tyNameVar = Var tyName in
            (
                Pi
                "_"
                (foldl
                    (\fun argName -> App fun $ Var argName)
                    tyNameVar
                    (reverse kindArgNames)
                )
                Type,
                k
            )
        predicateType k tyName kindArgNames ((argName, argType) : rest) =
            let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k) in
            let (tail, k'') = predicateType k' tyName (var : kindArgNames) rest in
            -- isn't there a bit more bookkeeping to do if arrows are dependent?
            --                        \/ here
            (Pi var argType tail, k'')
    
        consInductionArgType ::
            Int -> String -> String -> ConstructorSig 
                -> [String] -> [(String, Expr)] -> Result (Expr, Int)

        consInductionArgType k predicateName consName consSig argNames [] = do
            let consNameVar = Var consName
            let predicateNameVar = Var predicateName
            let caseRet = foldl (\fun argName -> App fun $ Var argName) consNameVar (reverse argNames)
            let (ConsPoint _ consKindArgs) = consSig

            consKindArgs <- mapM (readbackShow 0) consKindArgs
            let predicateKindArgs = foldl App predicateNameVar (reverse consKindArgs)
            return (App predicateKindArgs caseRet, k)

        consInductionArgType k predicateName consName consSig argNames ((argName, argType) : rest) =
            case consInductionArgTypeArgs tyName argType of
                Just argTypeArgs -> consInductionArgTypeIsInd argTypeArgs
                _ -> consInductionArgTypeIsNotInd

            where
                consInductionArgTypeIsInd :: [Expr] -> Result (Expr, Int)
                consInductionArgTypeIsInd argTypeArgs = do
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k)
                    (tail, k'') <- consInductionArgType k' predicateName consName consSig (var : argNames) rest
                    let predicateNameVar = Var predicateName
                    let predicatePartialInstance = foldl App predicateNameVar argTypeArgs
                    let predicateInstance = App predicatePartialInstance (Var var)
                    let tail' = Pi "_" predicateInstance tail
                    return (Pi var argType tail', k'')

                consInductionArgTypeIsNotInd :: Result (Expr, Int)
                consInductionArgTypeIsNotInd = do
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k)
                    (tail, k'') <- consInductionArgType k' predicateName consName consSig (var : argNames) rest
                    -- same objection as in predicateType
                    return (Pi var argType tail, k'')
            
                consInductionArgTypeArgs :: String -> Expr -> Maybe [Expr]
                consInductionArgTypeArgs tyName (Var f) | f == tyName = Just []
                consInductionArgTypeArgs tyName (App f arg) = do
                    firstArgs <- consInductionArgTypeArgs tyName f
                    return $ arg : firstArgs
                consInductionArgTypeArgs _ _ = Nothing

        inductionType :: String -> [(String, Expr)] -> [(String, ConstructorSig)] -> Result Expr
        inductionType tyName kindArgs consSigs = do
            let (pTy, _) = predicateType 0 tyName [] kindArgs
            (tail, _) <- inductionTypeCases 0 consSigs
            return $ Pi "P" pTy tail

            where
                inductionTypeCases :: Int -> [(String, ConstructorSig)] -> Result (Expr, Int)
                inductionTypeCases k [] =
                    return (inductionTypeTail k [] kindArgs)

                inductionTypeCases k ((consName, consSig@(ConsPoint consArgs _)) : rest) = do
                    (tail, k') <- inductionTypeCases k rest
                    consArgs <- mapM (\(name, val) -> do
                            val <- readbackShow 0 val
                            return (name, val)
                        ) consArgs
                    (head, k'') <- consInductionArgType k' "P" consName consSig [] consArgs
                    return (Pi "_" head tail, k'')

                inductionTypeTail :: Int -> [String] -> [(String, Expr)]  -> (Expr, Int)
                inductionTypeTail k kindArgNames [] =
                    let var = fresh k in
                    let tyNameVar = Var tyName in
                    let valTail = foldl (\fun argName -> App fun $ Var argName) tyNameVar (reverse kindArgNames) in
                    let predTail = foldl (\fun argName -> App fun $ Var argName) (Var "P") (reverse $ var : kindArgNames) in
                    (Pi var valTail predTail, k+1)
                inductionTypeTail k kindArgNames ((argName, argType) : rest) =
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k) in
                    let (tail, k'') = inductionTypeTail k' (var : kindArgNames) rest in
                    (Pi var argType tail, k'')
        
        inductionClosure :: String -> Int -> Value
        inductionClosure tyName arity =
            VFun Nothing (funVal arity [])
            where
                -- HOAS go brrrrrrr
                funVal :: Int -> [Value] -> Value -> Result Value
                funVal 1 args x = return $ VInd tyName $ reverse (x : args)
                funVal n args x = return $ VFun Nothing $ funVal (n-1) (x : args)

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
