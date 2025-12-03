module Ast (Expr(..), Stmt(..)) where

import Data.List

data Expr =
    Var String
  | Fun String Expr
  | App Expr Expr
  | Pi String Expr Expr
  | Type
  | Ind String Expr [Expr] -- contructed only through readback for type checking
  deriving Eq

data Stmt =
    Declaration String (Maybe Expr) Expr
  | Axiom String Expr
  | IndDecl String Expr [(String, Expr)]
  deriving Show

instance Show Expr where
    show (Var x) = x
    show (Fun x e) = "(fun " ++ x ++ " -> " ++ show e ++ ")"
    show (App f a) = "(" ++ showApp f [a] ++ ")"
        where
            showApp (App f a) tail = showApp f (a : tail)
            showApp fun args = show fun ++ " " ++ intercalate " " (map show args)

    show (Pi "_" t@(Fun _ _)  b) = "(" ++ show t ++ ") -> " ++ show b
    show (Pi "_" t@(Pi _ _ _) b) = "(" ++ show t ++ ") -> " ++ show b
    show (Pi "_" t            b) = show t ++ " -> " ++ show b
    show (Pi a   t            b) = "(" ++ a ++ ": " ++ show t ++ ") -> " ++ show b
    
    show Type = "Type"
