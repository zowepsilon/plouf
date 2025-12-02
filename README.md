## Plouf


#### Syntax

```bnf
program := stmt*

stmt := "axiom" ident ":" expr
      | ident (":" expr)? ":=" expr

expr := fun ident "->" expr
      | (ident: expr) -> expr
      | piExpr

piExpr := app
        | app -> expr

app := primary+

primary := ident
         | (expr)
         | "Type"
```
