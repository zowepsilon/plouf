module Main where
import Data.Char
-- import Debug.Trace
-- import Data.Maybe

import Typer

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
  | Unknown Char
  deriving (Show, Eq)

isIdentStart :: Char -> Bool
isIdentCont  :: Char -> Bool
isIdentStart c = c == '_' || isAlpha c
isIdentCont  c = c == '_' || isAlphaNum c

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
        toKeyword name = Ident name

        tokenizeNumLit [] = ([], [])
        tokenizeNumLit (c : rest) =
            if isDigit c then
                let (ident, rest') = tokenizeNumLit rest in
                (c : ident, rest')
            else
                ([], (c : rest))

type IndentLevel = Int

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

parseExpr    :: IndentLevel -> [Token] -> Maybe (Expr, [Token])
parseExprApp :: IndentLevel -> [Token] -> Maybe (Expr, [Token])
parseApp     :: IndentLevel -> [Token] -> Maybe (Expr, [Token])
parsePrimary :: IndentLevel -> [Token] -> Maybe (Expr, [Token])

-- parseExprApp l tokens | trace ("parseExprApp " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parseExprApp l tokens = do
    (left, rest) <- parseApp l tokens
    case rest of
        (Newline i : Arrow : rest) | l <= i -> do
            (right, rest) <- parseExpr l rest
            return (Pi "_" left right, rest)
        (Arrow : rest) -> do
            (right, rest) <- parseExpr l rest
            return (Pi "_" left right, rest)
        _ -> return (left, rest)


-- parseExpr l tokens | trace ("parseExpr " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
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
        Nothing -> parseExprApp l tokens
    where
        tryPiType rest = do
            rest <- ignoreNewline l rest
            (Ident var : rest) <- return rest
            rest <- ignoreNewline l rest
            (Colon : rest) <- return rest
            rest <- ignoreNewline l rest
            return (var, rest)
            
parseExpr l tokens = parseExprApp l tokens

-- parseApp l tokens | trace ("parseApp " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parseApp l tokens = do
    (left, rest) <- parsePrimary l tokens
    parseArg left rest
    where
        -- parseArg left tokens | trace ("parseArg " ++ show left ++ " " ++ show (listToMaybe tokens)) False = undefined
        parseArg left (Newline i : rest) | l <= i = parseArg left rest
        parseArg left tokens@(ParenOpen : _)      = parseArgContinue left tokens
        parseArg left tokens@(Ident _   : _)      = parseArgContinue left tokens
        parseArg left tokens@(KwType    : _)      = parseArgContinue left tokens
        parseArg left tokens                      = return (left, tokens)

        parseArgContinue left tokens = do
            (right, rest) <- parsePrimary l tokens
            parseArg (App left right) rest

-- parsePrimary l tokens | trace ("parsePrimary " ++ show l ++ " " ++ show (listToMaybe tokens)) False = undefined
parsePrimary l (Newline i : rest) = do checkNewline l i; parsePrimary l rest
parsePrimary _ ((Ident name) : rest) = return (Var name, rest)
parsePrimary l (ParenOpen : rest) = do
    (inner, rest) <- parseExpr l rest
    rest <- ignoreNewline l rest
    (ParenClose : rest) <- return rest
    return (inner, rest)
parsePrimary l (KwType : rest) = do
    rest <- ignoreNewline l rest
    (SqBraOpen : rest) <- return rest

    rest <- ignoreNewline l rest
    (NumLit i : rest) <- return rest

    rest <- ignoreNewline l rest
    (SqBraClose : rest) <- return rest

    return (Type i, rest)
parsePrimary _ _ = Nothing

testCheck :: Maybe ()
testCheck = do
    let id_expr = Fun "A" (Fun "x" (Var "x"))
    id_type <- evalExpr [] $ Pi "A" (Type 0) (Pi "_" (Var "A") (Var "A"))
    checkExpr 0 [] [] id_expr id_type

main :: IO ()
main = do
    source <- readFile "test.plf"
    let tokens = tokenize source
    let expr = parseExpr 4 tokens
    print expr
