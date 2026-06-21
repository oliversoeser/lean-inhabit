-- Syntax
structure Atom where (sym : String)

inductive Literal where
  | pos (a : Atom)
  | neg (a : Atom)

inductive Formula where
  | top
  | btm
  | atom (a : Atom)
  | not (f : Formula)
  | or (l r : Formula)
  | and (l r : Formula)
  | imp (l r : Formula)
  | xor (l r : Formula)
  | iff (l r : Formula)

def GenClause := List Formula
def StdClause := List Literal

-- Semantics
abbrev Interpret := Atom → Bool

def Formula.eval (i : Interpret) (f : Formula) : Bool :=
  match f with
  | top => true
  | btm => false
  | atom a => i a
  | not f => .not (f.eval i)
  | or l r => .or (l.eval i) (r.eval i)
  | and l r => .and (l.eval i) (r.eval i)
  | imp l r => .or (.not (l.eval i)) (r.eval i)
  | xor l r => l.eval i != r.eval i
  | iff l r => l.eval i == r.eval i

def Literal.eval (i : Interpret) (lit : Literal) : Bool :=
  match lit with
  | .pos a => i a
  | .neg a => not (i a)

def GenClause.eval (i : Interpret) (gc : GenClause) : Bool :=
  (gc.map (Formula.eval i)).foldl .or false

def StdClause.eval (i : Interpret) (sc : StdClause) : Bool :=
  (sc.map (Literal.eval i)).foldl .or false
