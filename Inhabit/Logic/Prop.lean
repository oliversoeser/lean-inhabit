namespace PropLogic

-- Syntax
abbrev Atom := String

inductive Formula where
  | var (a : Atom)
  | not (a : Formula)
  | and (a b : Formula)
  | or (a b : Formula)

inductive Literal where
  | pos (a : Atom)
  | neg (a : Atom)

abbrev SClause := List Literal

-- Semantics
abbrev Interpret := Atom → Bool

def List.interp (l : List String) : Interpret := l.contains

def prop_eval (f : Formula) (i : Interpret) : Bool :=
  match f with
  | .var name => i name
  | .not a => not (prop_eval a i)
  | .and a b => and (prop_eval a i) (prop_eval b i)
  | .or a b => or (prop_eval a i) (prop_eval b i)
