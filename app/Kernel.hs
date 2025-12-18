module Kernel(M, Error, State, emptyState, runStatement, runProgram) where

import System.IO
import Data.List
import GHC.Data.List.SetOps
import Debug.Trace

import Ast

evalExpr :: State -> Expr -> M Value
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
    evalAppVal state f x

evalExpr state (Pi x implicit t e)  = do
    t <- evalExpr state t
    return $ VPi (Just x) implicit t (\v -> evalExpr (addToEnv state x v) e)

evalExpr state (NoInfer e) = evalExpr state e
evalExpr state e@(Ind _ _) = Left $ Unreachable state ("tried to evalExpr " ++ show e)
evalExpr state e@(By _)    = Left $ Unreachable state ("tried to evalExpr " ++ show e)

evalAppVal :: State -> Value -> Value -> M Value
evalAppVal state f x =
    case f of
        (VFun _ f) -> f x
        (VNeutral f) -> return $ VNeutral (NApp f x)
        (VInd tyName branches) -> do
            (Inductive _ sigs) <- case assocMaybe (indTypes state) tyName of
                Just indTy -> return indTy
                Nothing -> Left $ UnknownInductiveType state tyName
            case x of
                VNeutral n -> case normalizedArg n of
                    Just (consName, consArgsRev) ->
                        let consArgs = reverse consArgsRev in
                        case assocMaybe sigs consName of
                            Just (ConsPoint _ isRecArgs _) -> do
                                consIndex <- case findIndex ((consName ==) . fst) sigs of
                                    Just i -> return i
                                    Nothing -> Left $ error "unreachable"

                                let branch = branches !! (consIndex + 1)
                                consArgs <- evalConsArgs (zip consArgs isRecArgs)

                                evalBranch branch consArgs
                            Nothing -> abortEval n
                    Nothing -> abortEval n
                _ -> Left $ RecursorArgumentIsNotAConstructor state x

            where
                abortEval n = return $ VNeutral $ NIndApp tyName branches n

                normalizedArg :: Neutral -> Maybe (String, [Value])
                normalizedArg (NVar consName) = return (consName, [])
                normalizedArg (NApp head arg) = do
                    (consName, headArgs) <- normalizedArg head
                    return (consName, arg : headArgs)
                normalizedArg (NIndApp _ _ _) = Nothing

                evalConsArgs :: [(Value, Bool)] -> M [Value]
                evalConsArgs [] = return []
                evalConsArgs ((arg, False) : rest) = do
                    rest <- evalConsArgs rest
                    return (arg : rest)
                evalConsArgs ((arg, True) : rest) = do
                    prev <- evalAppVal state f arg
                    rest <- evalConsArgs rest
                    return (arg : prev : rest)

                evalBranch :: Value -> [Value] -> M Value
                evalBranch val [] = return val
                evalBranch val (arg : rest) = do
                    val <- evalAppVal state val arg
                    evalBranch val rest

        _ -> Left $ AppOnNonFun state f x

neutral :: Int -> Neutral -> M Expr
neutral _ (NVar x)   = return $ Var x
neutral k (NApp f x) = do
    f <- neutral k f
    x <- readback k x
    return (App f x)
neutral k (NIndApp tyName branches x) = do
    branches <- mapM (readback k) branches
    x <- neutral k x
    return $ App (Ind tyName branches) x

readback :: Int -> Value -> M Expr
readback k (VFun _ f) = do
    let x = fresh k
    f <- f $ VNeutral $ NVar x
    f <- readback (k+1) f
    return (Fun x f)

readback k (VPi _ implicit a b) = do
    let x = fresh k
    b <- b (VNeutral $ NVar x)
    b <- readback (k+1) b
    a <- readback k a
    return (Pi x implicit a b)

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

inferExpr :: Int -> State -> Expr -> M Value
inferExpr _ state (Var x) =
    case assocMaybe (tenv state) x of
        Just ty -> return ty
        Nothing -> Left $ UnknownVariableTyping state x

inferExpr k state (App fun arg) =
    case inferExpr k state fun of
        Right (VPi _ _ a b) -> do
            arg <- checkExpr k state arg a
            arg <- evalExpr state arg
            b arg -- dependent types!!!
        Right ty -> Left $ CannotTypeAppWithoutPi state (App fun arg) ty
        Left err -> Left err

inferExpr k state (Pi x _ a b) = do
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
inferExpr k state (NoInfer e) = inferExpr k state e
inferExpr _ state f@(Fun _ _) = Left $ CannotInferTypeOfFun state f
inferExpr _ state f@(By  _  ) = Left $ CannotInferTypeOfBy  state f
inferExpr _ state e@(Ind _ _) = Left $ Unreachable state ("tried to inferExpr " ++ show e)


checkExpr :: Int -> State -> Expr -> Value -> M Expr

-- checkExpr _ state expr ty | traceShow ("checkExpr", expr, ty) False = undefined
checkExpr k state (Fun x e) (VPi _ _ a b) = do
    let y = VNeutral (NVar x)
    b <- (b y)
    let state' = addToTEnv state x a
    let state'' = addToEnv state' x y
    e <- checkExpr (k+1) state'' e b
    return (Fun x e)

checkExpr k state (By stmts) ty = do
    (builtExpr, tacRest) <- buildWithTactics k state stmts ty
    if not (null tacRest)
        then Left $ RemainingTactics state tacRest
        else return ()
    -- termination: buildWithTactics does not produce any By constructors
    case checkExpr k state builtExpr ty of
        Right e  -> Right e
        Left err -> Left $ IncorrectlyBuiltExpression stmts err

checkExpr k state (Var x) expectedTy = do
    case assocMaybe (tenv state) x of
        Nothing -> Left $ UnknownVariableTyping state x
        Just funTy@(VPi _ True _ _) -> do
            funTy <- readback k funTy
            expectedTyExpr <- readback k expectedTy
            let concreteTypes = [Right expectedTyExpr]
            let (iArgs, sigTypes) = argTypes funTy
            (inferredFunExpr, iArgExprs) <- inferImplicitArg (NoInfer $ Var x) iArgs concreteTypes sigTypes
            state <- addIArgsToState state (zip iArgs iArgExprs)
            checkByInferExpr k state inferredFunExpr expectedTy

        Just ty -> checkByInferExpr k state (Var x) ty

checkExpr k state (App f x) expectedTy = do
    let (funExpr, revArgs) = unfoldCall f x
    let args = reverse revArgs
    case funExpr of
        NoInfer _ -> checkByInferExpr k state (App f x) expectedTy
        _ -> case inferExpr k state funExpr of
            Right (VPi _ False _ _) -> checkByInferExpr k state (App f x) expectedTy
            Right funTy@(VPi _ True _ _) -> do
                funTy <- readback k funTy
                expectedTyExpr <- readback k expectedTy
                let concreteTypes = (map (\arg -> inferExpr k state arg >>= readback k) args) ++ [Right expectedTyExpr]
                let (iArgs, sigTypes) = argTypes funTy
                (inferredFunExpr, iArgExprs) <- inferImplicitArg (NoInfer funExpr) iArgs concreteTypes sigTypes
                state <- addIArgsToState state (zip iArgs iArgExprs)
                let inferredAppExpr = reconstructApps inferredFunExpr args
                checkByInferExpr k state inferredAppExpr expectedTy
                
            Right ty -> Left $ CannotTypeAppWithoutPi state (App f x) ty
            Left err -> Left err
        

checkExpr k state e t = checkByInferExpr k state e t

checkByInferExpr :: Int -> State -> Expr -> Value -> M Expr
checkByInferExpr k state e t = do
    t' <- inferExpr k state e
    if (veq k t t')
        then return e
        else Left $ MismatchedTypes state t t'

reconstructApps :: Expr -> [Expr] -> Expr
reconstructApps fun [] = fun
reconstructApps fun (arg : rest) = reconstructApps (App fun arg) rest

unfoldCall :: Expr -> Expr -> (Expr, [Expr])
unfoldCall (App f x) y =
    let (fun, args) = unfoldCall f x in
    (fun, y : args)
unfoldCall f x = (f, [x])

argTypes :: Expr -> ([(String, Expr)], [Expr])
argTypes (Pi x True a b) =
    let (iArgs, eArgTypes) = argTypes b in
    ((x, a) : iArgs, eArgTypes)
argTypes ty = ([], explicitArgTypesTail ty)
    where
        explicitArgTypesTail :: Expr -> [Expr]
        explicitArgTypesTail (Pi _ _ a b) = a : explicitArgTypesTail b
        explicitArgTypesTail ty = [ty]

inferImplicitArg :: Expr -> [(String, Expr)] -> [M Expr] -> [Expr] -> M (Expr, [Expr])
inferImplicitArg funExpr [] _ _ = return (funExpr, [])
inferImplicitArg funExpr ((varName, varTy) : iArgsRest) concreteTypes sigTypes = do
    implicitArg <- tryUnify varName concreteTypes sigTypes
    case implicitArg of
        Nothing -> Left $ UnconstraintedImplicitArg varName varTy concreteTypes sigTypes
        Just arg -> do
            (expr, argTail) <- inferImplicitArg (App funExpr arg) iArgsRest concreteTypes sigTypes
            return (expr, arg : argTail)

tryUnify :: String -> [M Expr] -> [Expr] -> M (Maybe Expr)
tryUnify _ [] _ = return Nothing
tryUnify _ _ [] = return Nothing
tryUnify varName (Right ccTy : concreteTypesRest) (sgTy : sigTypesRest) = do
    maybeArg <- unifySingleVar varName ccTy sgTy
    case maybeArg of
        Just arg -> return (Just arg)
        Nothing -> tryUnify varName concreteTypesRest sigTypesRest

tryUnify varName (Left _ : concreteTypesRest) (_ : sigTypesRest) =
    tryUnify varName concreteTypesRest sigTypesRest


unifySingleVar :: String -> Expr -> Expr -> M (Maybe Expr)
-- unifySingleVar varName t1 t2 | traceShow ("unifySingleVar", varName, t1, t2) False = undefined
unifySingleVar varName (Var x) expr | (x == varName) = return $ Just expr
unifySingleVar varName expr (Var x) | (x == varName) = return $ Just expr
unifySingleVar _ (Var _) _ = return Nothing
unifySingleVar _ _ (Var _) = return Nothing

unifySingleVar varName (Fun x e) (Fun x' e') = do
    if x == x' then return () else Left $ UnificationFailure (Fun x e) (Fun x' e')
    unifySingleVar varName e e'

unifySingleVar varName (App e1 e2) (App e1' e2') = do
    arg <- unifySingleVar varName e1 e1'
    case arg of
        Just arg -> return (Just arg)
        Nothing -> unifySingleVar varName e2 e2'

unifySingleVar varName e@(Pi x _ a b) e'@(Pi x' _ a' b') = do
    if x == x' then return () else Left $ UnificationFailure e e'
    arg <- unifySingleVar varName a a'
    case arg of
        Just arg -> return (Just arg)
        Nothing -> unifySingleVar varName b b'

unifySingleVar _ Type Type = return Nothing
unifySingleVar varName e@(Ind tyName args) e'@(Ind tyName' args') = do
    if tyName == tyName' then return () else Left $ UnificationFailure e e'
    unifyIndArgs varName e e' args args'

unifySingleVar _ e e' = Left $ UnificationFailure e e'
        
unifyIndArgs :: String -> Expr -> Expr -> [Expr] -> [Expr] -> M (Maybe Expr)
unifyIndArgs _ _ _ [] [] = return Nothing
unifyIndArgs _ e e' [] _ = Left $ UnificationFailure e e'
unifyIndArgs _ e e' _ [] = Left $ UnificationFailure e e'

unifyIndArgs varName e e' (a : rest) (a' : rest') = do
    arg <- unifySingleVar varName a a'
    case arg of
        Just arg -> return (Just arg)
        Nothing -> unifyIndArgs varName e e' rest rest'

addIArgsToState :: State -> [((String, Expr), Expr)] -> M State
addIArgsToState state [] = return state
addIArgsToState state (((argName, argTy), argExpr) : rest) = do
    argTyVal <- evalExpr state argTy
    argVal <- evalExpr state argExpr
    let state' = addToEnv (addToTEnv state argName argTyVal) argName argVal
    addIArgsToState state' rest

buildWithTactics :: Int -> State -> [TacticStmt] -> Value -> M (Expr, [TacticStmt])

-- buildWithTactics _ _ stmts ty | trace ("buildWithTactics (" ++ show stmts ++ ", " ++ show ty ++ ")") False = undefined
buildWithTactics k state (TacIntro names : tacRest) ty = do
    -- TODO: invalid empty intro
    buildFun state names ty tacRest
    where
        buildFun :: State -> [String] -> Value -> [TacticStmt] -> M (Expr, [TacticStmt])
        buildFun state [] ty tacRest = buildWithTactics k state tacRest ty
        buildFun state (name : nRest) (VPi _ _ a b) tacRest = do
            let var = VNeutral (NVar name)
            b <- (b var)
            let state' = addToTEnv state name a
            let state'' = addToEnv state' name var
            (body, tacRest) <- buildFun state'' nRest b tacRest
            return (Fun name body, tacRest)
        buildFun state (name : _) ty _ = Left $ IntroTacticOnNonPi state (TacIntro names) name ty

buildWithTactics k state (TacUse funExpr : tacRest) ty = do
    fty <- inferExpr k state funExpr
    buildApp funExpr fty tacRest
    where
        buildApp :: Expr -> Value -> [TacticStmt] -> M (Expr, [TacticStmt])
        -- buildApp expr ty tacRest | traceShow ("buildApp", expr, ty, tacRest) False = undefined

        buildApp expr funTy tacRest | veq k funTy ty = do
            expr <- checkExpr k state expr ty
            return (expr, tacRest)

        buildApp funExpr funTy@(VPi _ True _ _) tacRest = do
            funTy <- readback k funTy
            expectedTyExpr <- readback k ty
            let concreteTypes = [Right expectedTyExpr]
            let (iArgs, eArgs, sigTypes) = retType funTy
            (inferredFunExpr, iArgExprs) <- inferImplicitArg (NoInfer funExpr) iArgs concreteTypes sigTypes
            state <- addIArgsToState state (zip iArgs iArgExprs)
            (eArgs, tacRest) <- explicitArgHoles state eArgs tacRest
            return (reconstructApps inferredFunExpr eArgs, tacRest)
            
        buildApp funExpr (VPi _ False a b) tacRest = do
            (arg, tacRest) <- buildWithTactics k state tacRest a
            argVal <- evalExpr state arg
            b <- b argVal
            buildApp (App funExpr arg) b tacRest

        buildApp _ fty _ = Left $ MismatchedTypesInUseTactic state ty fty
    
        explicitArgHoles :: State -> [Expr] -> [TacticStmt] -> M ([Expr], [TacticStmt])
        explicitArgHoles _ [] tacRest = return ([], tacRest)
        explicitArgHoles state (ty : rest) tacRest = do
            ty <- evalExpr state ty
            (arg, tacRest) <- buildWithTactics k state tacRest ty
            (argsTail, tacRest) <- explicitArgHoles state rest tacRest
            return (arg : argsTail, tacRest)


        retType :: Expr -> ([(String, Expr)], [Expr], [Expr])
        retType (Pi x True a b) =
            let (iArgs, eArgTypes, ret) = retType b in
            ((x, a) : iArgs, eArgTypes, ret)
        retType ty = 
            let (eargs, ret) = retTypeTail ty in
            ([], eargs, ret)

        retTypeTail :: Expr -> ([Expr], [Expr])
        retTypeTail (Pi _ _ a b) =
            let (eargs, ret) = retTypeTail b in
            (a : eargs, ret)
        retTypeTail ty = ([], [ty])


buildWithTactics k state (TacInduction : tacRest) ty = do
    tyExpr <- readback k ty
    case tyExpr of
        (Pi x _ (Var tyName) b) ->
            let indTac = TacUse $ App (Var $ tyName ++ ".ind") (Fun x b) in
            buildWithTactics k state (indTac : tacRest) ty
        _ -> Left $ CannotUseInductionTactic state ty

buildWithTactics _ state [] ty = Left $ UnfilledHole state ty


evalArgList :: State -> [(String, Expr)] -> M ([(String, Value)], State)
evalArgList state [] = return ([], state)
evalArgList state ((argName, argTy) : rest) = do
    argTy <- evalExpr state argTy
    let state' = addOpaque state argName argTy
    (rest, state'') <- evalArgList state' rest
    return ((argName, argTy) : rest, state'')

runStatement :: State -> Stmt -> M (State, String)
runStatement state (Axiom name ty) = do
    ty <- checkExpr 0 state ty VType
    ty <- evalExpr state ty
    let msg = "axiom " ++ name ++ ": " ++ show ty
    return (addOpaque state name ty, msg)

runStatement state (Print expr) = do
    ty <- inferExpr 0 state expr
    val <- evalExpr state expr
    let msg = show expr ++ ": " ++ show ty ++ "\n    = " ++ show val
    return (state, msg)

runStatement state (IndDecl tyName kind constructors) = do
    kind <- checkExpr 0 state kind VType
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

    let state1 = addOpaque state tyName kindVal
    (consSigs, consTypes) <- unzip <$> mapM (evalCons state1) constructors
    (consTypesVal, _) <- evalArgList state1 consTypes

    let state2 = foldl (\state (consName, consTy) -> addOpaque state consName consTy) state1 consTypesVal

    let indName = (tyName ++ ".ind")
    -- predicate + cases + type arguments for value
    let indArity = 1 + length kindArgs + length consSigs
    (indTy, consSigs) <- inductionType tyName kindArgs consSigs
    indTy <- evalExpr state2 indTy
    let state3 = addToTEnv state2 indName indTy
    let state4 = addToEnv state3 indName (inductionClosure tyName indArity)

    let ind = Inductive kindArgsVal consSigs
    let state5 = addInductive state4 tyName ind

    let msg = "inductive " ++ tyName ++ ": " ++ show kindVal
    return (state5, msg)

    where
        getKindArgs :: Expr -> M [(String, Expr)]
        getKindArgs (Pi a _ t b) = do
            args <- getKindArgs b
            return $ (a, t) : args
        getKindArgs Type = return []
        getKindArgs kind = Left (NonTypeInductiveKind state kind)

        evalCons :: State -> (String, Expr) -> M ((String, ConstructorSig), (String, Expr))
        evalCons state (consName, consTy) = do
            consTy <- checkExpr 0 state consTy VType
            consTyVal <- evalExpr state consTy
            consTy <- readbackShow 0 consTyVal
            (consArgs, consTyArgs) <- linearize consTy
            (consArgs, state) <- evalArgList state consArgs
            consTyArgs <- mapM (evalExpr state) consTyArgs
            return ((consName, ConsPoint consArgs [] consTyArgs), (consName, consTy))
        
        linearize :: Expr -> M ([(String, Expr)], [Expr])
        linearize (Pi a _ t b) = do -- TODO: implicit
            (args, tail) <- linearize b
            return ((a, t) : args, tail)
        linearize consTy = do
            tail <- linearizeTail tyName consTy
            return $ ([], tail)

        linearizeTail :: String -> Expr -> M [Expr]
        linearizeTail tyName (Var x) | x == tyName = return []
        linearizeTail tyName (App f arg) = do
            tail <- linearizeTail tyName f 
            return (arg : tail)
        linearizeTail _ ret = Left $ InvalidConstructorType state ret


        predicateType :: Int -> String -> [String] -> [(String, Expr)]  -> (Expr, Int)
        predicateType k tyName kindArgNames [] =
            let tyNameVar = Var tyName in
            (
                Pi
                "_"
                False
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
            (Pi var False argType tail, k'')
    
        consInductionArgType ::
            Int -> String -> String -> ConstructorSig 
                -> [String] -> [(String, Expr)] -> M (Expr, Int, [Bool])

        consInductionArgType k predicateName consName consSig argNames [] = do
            let consNameVar = Var consName
            let predicateNameVar = Var predicateName
            let caseRet = foldl (\fun argName -> App fun $ Var argName) consNameVar (reverse argNames)
            let (ConsPoint _ _ consKindArgs) = consSig

            consKindArgs <- mapM (readbackShow 0) consKindArgs
            let predicateKindArgs = foldl App predicateNameVar (reverse consKindArgs)
            return (App predicateKindArgs caseRet, k, [])

        consInductionArgType k predicateName consName consSig argNames ((argName, argType) : rest) =
            case consInductionArgTypeArgs tyName argType of
                Just argTypeArgs -> consInductionArgTypeIsInd argTypeArgs
                _ -> consInductionArgTypeIsNotInd

            where
                consInductionArgTypeIsInd :: [Expr] -> M (Expr, Int, [Bool])
                consInductionArgTypeIsInd argTypeArgs = do
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k)
                    (tail, k'', isRecTail) <- consInductionArgType k' predicateName consName consSig (var : argNames) rest
                    let predicateNameVar = Var predicateName
                    let predicatePartialInstance = foldl App predicateNameVar argTypeArgs
                    let predicateInstance = App predicatePartialInstance (Var var)
                    let tail' = Pi "_" False predicateInstance tail
                    return (Pi var False argType tail', k'', True : isRecTail)

                consInductionArgTypeIsNotInd :: M (Expr, Int, [Bool])
                consInductionArgTypeIsNotInd = do
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k)
                    (tail, k'', isRecTail) <- consInductionArgType k' predicateName consName consSig (var : argNames) rest
                    -- same objection as in predicateType
                    return (Pi var False argType tail, k'', False : isRecTail)
            
                consInductionArgTypeArgs :: String -> Expr -> Maybe [Expr]
                consInductionArgTypeArgs tyName (Var f) | f == tyName = Just []
                consInductionArgTypeArgs tyName (App f arg) = do
                    firstArgs <- consInductionArgTypeArgs tyName f
                    return $ arg : firstArgs
                consInductionArgTypeArgs _ _ = Nothing

        inductionType :: String -> [(String, Expr)] -> [(String, ConstructorSig)] -> M (Expr, [(String, ConstructorSig)])
        inductionType tyName kindArgs consSigs = do
            let (pTy, _) = predicateType 0 tyName [] kindArgs
            (tail, _, isRecArgsList) <- inductionTypeCases 0 consSigs
            let consSigs' = map (\((consName, ConsPoint consArgs _ kindArgs), isRecArgs) -> (consName, ConsPoint consArgs isRecArgs kindArgs)) (zip consSigs isRecArgsList)
            return (Pi "P" False pTy tail, consSigs')

            where
                inductionTypeCases :: Int -> [(String, ConstructorSig)] -> M (Expr, Int, [[Bool]])
                inductionTypeCases k [] =
                    return (inductionTypeTail k [] kindArgs)

                inductionTypeCases k ((consName, consSig@(ConsPoint consArgs _ _)) : rest) = do
                    (tail, k', isRecArgsTail) <- inductionTypeCases k rest
                    consArgs <- mapM (\(name, val) -> do
                            val <- readbackShow 0 val
                            return (name, val)
                        ) consArgs
                    (head, k'', isRecArgs) <- consInductionArgType k' "P" consName consSig [] consArgs
                    return (Pi "_" False head tail, k'', isRecArgs : isRecArgsTail)

                inductionTypeTail :: Int -> [String] -> [(String, Expr)]  -> (Expr, Int, [[Bool]])
                inductionTypeTail k kindArgNames [] =
                    let var = fresh k in
                    let tyNameVar = Var tyName in
                    let valTail = foldl (\fun argName -> App fun $ Var argName) tyNameVar (reverse kindArgNames) in
                    let predTail = foldl (\fun argName -> App fun $ Var argName) (Var "P") (reverse $ var : kindArgNames) in
                    (Pi var False valTail predTail, k+1, [])
                inductionTypeTail k kindArgNames ((argName, argType) : rest) =
                    let (var, k') = if argName == "_" then (fresh k, k+1) else (argName, k) in
                    let (tail, k'', _) = inductionTypeTail k' (var : kindArgNames) rest in
                    (Pi var False argType tail, k'', [])
        
        inductionClosure :: String -> Int -> Value
        inductionClosure tyName arity =
            VFun Nothing (funVal arity [])
            where
                -- HOAS go brrrrrrr
                funVal :: Int -> [Value] -> Value -> M Value
                funVal 1 args x = return $ VInd tyName $ reverse (x : args)
                funVal n args x = return $ VFun Nothing $ funVal (n-1) (x : args)

runStatement state (Declaration name Nothing val) = do
    ty <- inferExpr 0 state val
    runDecl state name ty val

runStatement state (Declaration name (Just ty) val) = do
    ty <- checkExpr 0 state ty VType
    ty <- evalExpr state ty
    val <- checkExpr 0 state val ty
    runDecl state name ty val

runStatement state ExitStmt = return (state, "Exitted early!")

runDecl :: State -> String -> Value -> Expr -> M (State, String)
runDecl state name ty val = do
    val <- evalExpr state val
    let state' = addToTEnv state name ty
    let state'' = addToEnv state' name val
    let msg = name ++ ": " ++ show ty
    return (state'', msg)

runProgram :: State -> [Stmt] -> IO (M State)
runProgram state [] = return (return state)

runProgram state (ExitStmt : rest) = do
    _ <- getLine
    putStr "\x1b[A"
    hFlush stdout

    runProgram state rest

runProgram state (stmt : rest) =
    case runStatement state stmt of
        Right (state, "") -> runProgram state rest
        Right (state, msg) -> do
            putStrLn msg
            runProgram state rest
        Left err -> return $ Left err
