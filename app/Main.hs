module Main where
import Data.Char

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

parseExpr :: [Token] -> Maybe (Expr, [Token])
parseApp :: [Token] -> Maybe (Expr, [Token])
parsePrimary :: [Token] -> Maybe (Expr, [Token])

parseExpr (KwFun : rest) = do
    (Ident var : rest) <- return rest
    (Arrow : rest) <- return rest
    (body, rest) <- parseExpr rest
    return (Fun var body, rest)
parseExpr (ParenOpen : Ident var : Colon : rest) = do
    (arg_ty, rest) <- parseExpr rest
    (ParenClose : Arrow : rest) <- return rest
    (ret_ty, rest) <- parseExpr rest
    return (Pi var arg_ty ret_ty, rest)
parseExpr tokens = do
    (left, rest) <- parseApp tokens
    case rest of
        (Arrow : rest) -> do
            (right, rest) <- parseExpr rest
            return (Pi "_" left right, rest)
        _ -> return (left, rest)


parseApp tokens = do
    (left, rest) <- parsePrimary tokens
    parseArg left rest
    where
        parseArg left tokens@(ParenOpen : _) = parseArgContinue left tokens
        parseArg left tokens@(Ident _   : _) = parseArgContinue left tokens
        parseArg left tokens@(KwType    : _) = parseArgContinue left tokens
        parseArg left tokens                 = return (left, tokens)

        parseArgContinue left tokens = do
            (right, rest) <- parsePrimary tokens
            parseArg (App left right) rest

parsePrimary ((Ident name) : rest) = return (Var name, rest)
parsePrimary (ParenOpen : rest) = do
    (inner, rest) <- parseExpr rest
    (ParenClose : rest) <- return rest
    return (inner, rest)
parsePrimary (KwType : SqBraOpen : NumLit i : SqBraClose : rest) =
    return (Type i, rest)
parsePrimary _ = Nothing

testCheck :: IO ()
testCheck = do
    let id_expr = Fun "A" (Fun "x" (Var "x"))
    let Just id_type = evalExpr [] $ Pi "A" (Type 0) (Pi "_" (Var "A") (Var "A"))
    print $ check 0 [] [] id_expr id_type

main :: IO ()
main = do
    source <- readFile "test.plf"
    print $ parseExpr toks
