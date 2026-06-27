-- Terms
import Mathlib.Data.Finset.Defs

universe u v

inductive Term (σ : Nat → Sort u) (X : Type v) where
  | var (x : X)
  | app (n : Nat) (sym : σ n) (args : Fin n → Term σ X)

inductive Pos : Term σ X → Type u where
  | root : Pos t
  | node (n : Nat) (sym : σ n) (args : Fin n → Term σ X) (i : Fin n) (q : Pos (args i))
         : Pos (.app n sym args)

def Term.at (s : Term σ X) (p : Pos s) : Term σ X :=
  match p with
  | .root => s
  | .node _ _ args i q => (args i).at q

def Term.sub (s t : Term σ X) (p : Pos s) : Term σ X :=
  match p with
  | .root => t
  | .node n sym args i q =>
          .app n sym (λ k : Fin n => if i = k then (args i).sub t q else args k)

def Var (s : Term σ X) : Type u := { x : X // ∃ p : Pos s, s.at p = .var x }

abbrev Ground (σ : Nat → Sort u) := Term σ Empty

structure Substitution (σ : Nat → Sort u) (X : Type v) where
  (φ : X → Term σ X) (dom : Finset X) (h : ∀ x : X, x ∈ dom ↔ φ x ≠ .var x)

def Substitution.apply (s : Term σ X) (sub : Substitution σ X) : Term σ X :=
  match s with
  | .var x => sub.φ x
  | .app n sym args => .app n sym (λ i : Fin n => sub.apply (args i))

-- Universal Algebra

class Algebra (σ : Nat → Sort u) (A : Type v) where
  interpret : ∀ n : Nat, σ n → (Fin n → A) → A

