module Ast (Expr(..), Stmt(..)) where

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

    show (Pi "_" t@(Fun _ _)  b) = "(" ++ show t ++ ") -> " ++ show b
    show (Pi "_" t@(Pi _ _ _) b) = "(" ++ show t ++ ") -> " ++ show b
    show (Pi "_" t            b) = show t ++ " -> " ++ show b
    show (Pi a   t            b) = "(" ++ a ++ ": " ++ show t ++ ") -> " ++ show b
    
    show Type = "Type"
