## Plouf

A simple proof assistant featuring dependent types, general inductive types/type families and a basic tactic language.

There are two ways of using this proof assistant :

- Via a REPL, by passing no argument :

```shell
cabal run
```

(I would recommend using the REPL with `rlwrap` : `rlwrap cabal run`)

- By reading a source file :

```shell
cabal run exes -- examples/tacticTest.plf
```

An experimental (quite buggy) implementation of implicit argument inference can be found in the `implicit-args` branch.


#### Example

```haskell
// see examples/tacticTest.plf

// dependent types
id: (A: Type) -> A -> A := fun A x -> x

// inductive type
inductive Bool: Type
  tt: Bool
  ff: Bool

// inductive type family
inductive or: (A: Type) -> (B: Type) -> Type
  left:  (A: Type) -> (B: Type) -> A -> or A B
  right: (A: Type) -> (B: Type) -> B -> or A B

inductive eq: (A: Type) -> A -> A -> Type
  refl: (A: Type) -> (x: A) -> eq A x x


is_tt: Bool -> Type := fun b -> (eq Bool b tt)
is_ff: Bool -> Type := fun b -> (eq Bool b ff)

// tactic language
bool_is_two: (b: Bool) -> or (is_tt b) (is_ff b) := by
  induction
  - left (is_tt tt) (is_ff tt); refl Bool tt
  - right (is_tt ff) (is_ff ff); refl Bool ff
```


### Project structure

- `app/Main.hs`: entry point, REPL
- `app/Ast.hs`: shared data structures and some utils
- `app/Parser.hs`: the lexer/parser
- `app/Typer.hs`: dependent type checker, evaluator, and tactic language
- `examples/`: example programs
