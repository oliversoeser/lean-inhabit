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
def Interp := Atom → Prop

def Formula.eval (i : Interp) (f : Formula) : Prop :=
  match f with
  | top => True
  | btm => False
  | atom a => i a
  | not f => ¬(f.eval i)
  | or l r => (l.eval i) ∨ (r.eval i)
  | and l r => (l.eval i) ∧ (r.eval i)
  | imp l r => (l.eval i) → (r.eval i)

-- Logical Consequence
def Formula.entails (f g : Formula) : Prop :=
  ∀ i : Interp, f.eval i → g.eval i

def Formula.equiv (f g : Formula) : Prop :=
  ∀ i : Interp, f.eval i ↔ g.eval i

infix:60 " ⊨ " => fun l r => Formula.entails l r
infix:60 " ≃ " => fun l r => Formula.equiv l r
