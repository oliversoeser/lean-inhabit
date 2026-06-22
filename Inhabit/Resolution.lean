-- Syntax
structure Term where (sym : String) (ts : List Term)

structure Atom where (sym : String) (ts : List Term)

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

-- Clause Syntax
inductive Literal where
  | pos (a : Atom)
  | neg (a : Atom)

def GenClause := List Formula
def StdClause := List Literal

def Literal.toFormula (lit : Literal) : Formula :=
  match lit with
  | pos a => .atom a
  | neg a => .not (.atom a)

def GenClause.toFormula (gc : GenClause) : Formula :=
  match gc with
  | .nil => .btm
  | .cons h t => .or h (toFormula t)

def StdClause.toFormula (sc : StdClause) : Formula :=
  match sc with
  | .nil => .btm
  | .cons h t => .or h.toFormula (toFormula t)

-- Semantics
def Interp := Atom → Bool

def Formula.eval (i : Interp) (f : Formula) : Bool :=
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
