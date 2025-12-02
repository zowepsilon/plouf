module Unif where

import qualified Ast

data UExpr =
    UVar Integer
  | Var String
  | Fun String UExpr
  | App UExpr UExpr
  | Pi String UExpr UExpr
  | Type

exprToUExpr :: Expr -> UExpr
exprToUExpr (Ast.Var x)    = Var x
exprToUExpr (Ast.Fun x e)  = Fun x (exprToUExpr e)
exprToUExpr (Ast.App f x)  = App (exprToUExpr f) (exprToUExpr x)
exprToUExpr (Ast.Pi a t b) = Pi a (exprToUExpr t) (exprToUExpr b)
exprToUExpr Ast.Type       = Type
