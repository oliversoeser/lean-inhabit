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

def Literal.eval (i : Interp) (lit : Literal) : Bool :=
  match lit with
  | pos a => i a
  | neg a => not (i a)

def GenClause.eval (i : Interp) (gc : GenClause) : Bool :=
  (gc.map (Formula.eval i)).foldl .or false

def StdClause.eval (i : Interp) (sc : StdClause) : Bool :=
  (sc.map (Literal.eval i)).foldl .or false

-- Substitution
def Subst := Atom → Formula

def Formula.subst (σ : Subst) (f : Formula) :=
  match f with
  | top => top
  | btm => btm
  | atom a => σ a
  | not f => not (f.subst σ)
  | or l r => or (l.subst σ) (r.subst σ)
  | and l r => and (l.subst σ) (r.subst σ)
  | imp l r => imp (l.subst σ) (r.subst σ)
  | xor l r => xor (l.subst σ) (r.subst σ)
  | iff l r => iff (l.subst σ) (r.subst σ)

def Literal.subst (σ : Subst) (lit : Literal) :=
  match lit with
  | pos a => σ a
  | neg a => .not (σ a)
