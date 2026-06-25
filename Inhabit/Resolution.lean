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

-- Semantics
def Interp := Atom → Prop

@[simp] def Formula.eval (i : Interp) (f : Formula) : Prop :=
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

-- Substitution
inductive VarFormula where
  | top
  | btm
  | atom (a : Atom)
  | not (f : VarFormula)
  | or (l r : VarFormula)
  | and (l r : VarFormula)
  | imp (l r : VarFormula)
  | var (sym : String)

def FormSub := String → Formula

@[simp] def FormSub.apply (σ : FormSub) (f : VarFormula) : Formula :=
  match f with
  | .top => .top
  | .btm => .btm
  | .atom a => .atom a
  | .not f => .not (σ.apply f)
  | .or l r => .or (σ.apply l) (σ.apply r)
  | .and l r => .and (σ.apply l) (σ.apply r)
  | .imp l r => .imp (σ.apply l) (σ.apply r)
  | .var sym => σ sym

-- Inferences
structure Inference where (pres : List VarFormula) (conc : VarFormula)

def Inference.sound (inf : Inference) : Prop :=
  ∀ σ : FormSub, (inf.pres.foldl (λ f vf => .and f (σ.apply vf)) .top) ⊨ σ.apply inf.conc

def InferSys := List Inference

def InferSys.concs (is : InferSys) : List VarFormula :=
  is.map Inference.conc
