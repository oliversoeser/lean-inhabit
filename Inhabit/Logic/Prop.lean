-- Syntax
inductive PropLang where
  | Var (name : String)
  | Not (a : PropLang)
  | And (a b : PropLang)
  | Or (a b : PropLang)

-- Semantics
abbrev PropInterp := String → Bool

def List.interp (l : List String) : PropInterp := l.contains

def prop_eval (f : PropLang) (i : PropInterp) : Bool :=
  match f with
  | .Var name => i name
  | .Not a => not (prop_eval a i)
  | .And a b => and (prop_eval a i) (prop_eval b i)
  | .Or a b => or (prop_eval a i) (prop_eval b i)
