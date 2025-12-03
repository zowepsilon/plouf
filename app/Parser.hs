module Parser (parseProgram) where

import Data.Char
import Debug.Trace
import Data.Maybe

import Ast

enableDebug :: Bool
enableDebug = False

data Token =
    ColonEq
  | Colon
  | Eq
  | Arrow
  | Newline Int
  | ParenOpen
  | ParenClose
  | SqBraOpen
  | SqBraClose
  | Ident String
  | NumLit Integer
  | KwFun
  | KwType
  | KwAxiom
  | KwInductive
  | Unknown Char
  deriving (Show, Eq)

isIdentStart :: Char -> Bool
isIdentCont  :: Char -> Bool
isIdentStart c = c == '_' || isAlpha c
isIdentCont  c = c == '_' || c == '.' || isAlphaNum c

tokenize :: String -> [Token]
tokenize []               = []
tokenize (' '     : rest) = tokenize rest
tokenize (':':'=' : rest) = ColonEq : tokenize rest
tokenize (':'     : rest) = Colon : tokenize rest
tokenize ('='     : rest) = Eq : tokenize rest
tokenize ('-':'>' : rest) = Arrow : tokenize rest
tokenize ('\n'    : rest) = (Newline indent) : tokenize rest'
    where
        (indent, rest') = countIndent 0 rest
        countIndent acc (' ' : rest) = countIndent (acc+1) rest
        countIndent _  ('\n' : rest) = countIndent 0 rest
        countIndent acc rest = (acc, rest)
tokenize ('('     : rest) = ParenOpen  : tokenize rest
tokenize (')'     : rest) = ParenClose : tokenize rest
tokenize ('['     : rest) = SqBraOpen  : tokenize rest
tokenize (']'     : rest) = SqBraClose : tokenize rest
tokenize ('/':'/' : rest) = tokenize (skipLine rest)
    where skipLine [] = []
          skipLine ('\n' : rest) = rest
          skipLine (_ : rest) = skipLine rest
tokenize (c : rest)
    | isIdentStart c =
        let (ident, rest') = tokenizeIdent (c : rest) in
        toKeyword ident : tokenize rest'
    | isDigit c =
        let (num, rest') = tokenizeNumLit (c : rest) in
        NumLit (read num) : tokenize rest'
    | otherwise = Unknown c : tokenize rest
    where
        tokenizeIdent [] = ([], [])
        tokenizeIdent (c : rest) =
            if isIdentCont c then
                let (ident, rest') = tokenizeIdent rest in
                (c : ident, rest')
            else
                ([], (c : rest))
        toKeyword "fun" = KwFun
        toKeyword "Type" = KwType
        toKeyword "axiom" = KwAxiom
        toKeyword "inductive" = KwInductive
        toKeyword name = Ident name

        tokenizeNumLit [] = ([], [])
        tokenizeNumLit (c : rest) =
            if isDigit c then
                let (ident, rest') = tokenizeNumLit rest in
                (c : ident, rest')
            else
                ([], (c : rest))


type IndentLevel = Int

indentOffset :: IndentLevel
indentOffset = 4

checkNewline :: IndentLevel -> IndentLevel -> Maybe ()
checkNewline l i =
    if l <= i
    then Just ()
    else  Nothing

ignoreNewline :: IndentLevel -> [Token] -> Maybe [Token]
ignoreNewline l (Newline i : rest) =
    if l <= i
    then Just rest
    else Nothing
ignoreNewline _ tokens = Just tokens

parseProgram :: String -> Maybe [Stmt]
parseProgram = parseProgramTok . tokenize


parseProgramTok :: [Token] -> Maybe [Stmt]
parseStmt       :: IndentLevel -> [Token] -> Maybe (Stmt, [Token])
parseAnnot      :: IndentLevel -> [Token] -> Maybe (String, Expr, [Token])
parseExpr       :: IndentLevel -> [Token] -> Maybe (Expr, [Token])
parsePiExpr     :: IndentLevel -> [Token] -> Maybe (Expr, [Token])
parseApp        :: IndentLevel -> [Token] -> Maybe (Expr, [Token])
parsePrimary    :: IndentLevel -> [Token] -> Maybe (Expr, [Token])


parseProgramTok [] = Just []
parseProgramTok (Newline _ : rest) = parseProgramTok rest
parseProgramTok tokens = do
    (stmt, rest) <- parseStmt 0 tokens
    stmts <- parseProgramTok rest
    return (stmt : stmts)

parseStmt l tokens | enableDebug && trace ("parseStmt " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parseStmt _ [] = Nothing
parseStmt l (Newline i : rest) = do checkNewline l i; parseStmt l rest
parseStmt l (KwAxiom : rest) = do
    (name, ty, rest) <- parseAnnot (l+indentOffset) rest
    return (Axiom name ty, rest) 

parseStmt l (KwInductive : rest) = do
    rest <- ignoreNewline (l+indentOffset) rest
    (tyName, tyKind, rest) <- parseAnnot (l+2*indentOffset) rest

    (constructors, rest) <- parseConstructors (l+indentOffset) rest
    let stmt = IndDecl tyName tyKind constructors
    return (stmt, rest)

    where
        parseStmt l tokens
            | enableDebug && trace ("parseConstructors" ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
        parseConstructors :: IndentLevel -> [Token] -> Maybe ([(String, Expr)], [Token])
        parseConstructors l (Newline i : rest) | l <= i = do
            (consName, consTy, rest) <- parseAnnot (l+indentOffset) rest
            (others, rest) <- parseConstructors l rest
            return ((consName, consTy) : others, rest)
        parseConstructors l (Newline i : rest) = return ([], rest)
        parseConstructors _ _ = Nothing

parseStmt l (Ident name : ColonEq : rest) = do
    rest <- ignoreNewline (l+indentOffset) rest
    (value, rest) <- parseExpr (l+indentOffset) rest

    return (Declaration name Nothing value, rest)

parseStmt l tokens = do
    (name, ty, rest) <- parseAnnot (l+indentOffset) tokens

    rest <- ignoreNewline (l+indentOffset) rest
    (ColonEq : rest) <- return rest

    rest <- ignoreNewline (l+indentOffset) rest
    (value, rest) <- parseExpr (l+indentOffset) rest

    return (Declaration name (Just ty) value, rest)
parseStmt _ _ = Nothing

parseAnnot l (Ident name : Colon : rest) = do
    (ty, rest) <- parseExpr l rest
    return (name, ty, rest)
parseAnnot _ _ = Nothing

parseExpr l tokens | enableDebug && trace ("parseExpr " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parseExpr l (Newline i : rest) = do checkNewline l i; parseExpr l rest
parseExpr l (KwFun : rest) = do
    rest <- ignoreNewline l rest
    (Ident var : rest) <- return rest

    rest <- ignoreNewline l rest
    (Arrow : rest) <- return rest

    rest <- ignoreNewline l rest
    (body, rest) <- parseExpr l rest

    return (Fun var body, rest)
parseExpr l tokens@(ParenOpen : rest) = do
    case tryPiType rest of
        Just (var, rest) -> do
            (arg_ty, rest) <- parseExpr l rest

            rest <- ignoreNewline l rest
            (ParenClose : rest) <- return rest

            rest <- ignoreNewline l rest
            (Arrow : rest) <- return rest

            rest <- ignoreNewline l rest
            (ret_ty, rest) <- parseExpr l rest

            return (Pi var arg_ty ret_ty, rest)
        Nothing -> parsePiExpr l tokens
    where
        tryPiType rest = do
            rest <- ignoreNewline l rest
            (Ident var : rest) <- return rest
            rest <- ignoreNewline l rest
            (Colon : rest) <- return rest
            rest <- ignoreNewline l rest
            return (var, rest)
            
parseExpr l tokens = parsePiExpr l tokens

parsePiExpr l tokens | enableDebug && trace ("parsePiExpr " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parsePiExpr l tokens = do
    (left, rest) <- parseApp l tokens
    case rest of
        (Newline i : Arrow : rest) | l <= i -> do
            (right, rest) <- parseExpr l rest
            return (Pi "_" left right, rest)
        (Arrow : rest) -> do
            (right, rest) <- parseExpr l rest
            return (Pi "_" left right, rest)
        _ -> return (left, rest)

parseApp l tokens | enableDebug && trace ("parseApp " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parseApp l tokens = do
    (left, rest) <- parsePrimary l tokens
    parseArg left rest
    where
        parseArg left tokens | enableDebug && trace ("parseArg " ++ show left ++ " " ++ show (listToMaybe tokens)) False = undefined
        parseArg left (Newline i : rest) | l <= i = parseArg left rest
        parseArg left tokens@(ParenOpen : _)      = parseArgContinue left tokens
        parseArg left tokens@(Ident _   : _)      = parseArgContinue left tokens
        parseArg left tokens@(KwType    : _)      = parseArgContinue left tokens
        parseArg left tokens                      = return (left, tokens)

        parseArgContinue left tokens = do
            (right, rest) <- parsePrimary l tokens
            parseArg (App left right) rest

parsePrimary l tokens | enableDebug && trace ("parsePrimary " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parsePrimary l (Newline i : rest) = do checkNewline l i; parsePrimary l rest
parsePrimary _ ((Ident name) : rest) = return (Var name, rest)
parsePrimary l (ParenOpen : rest) = do
    (inner, rest) <- parseExpr l rest
    rest <- ignoreNewline l rest
    (ParenClose : rest) <- return rest
    return (inner, rest)
parsePrimary _ (KwType : rest) = return (Type, rest)
parsePrimary _ _ = Nothing
