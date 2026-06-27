-- Terms and Universal Algebra

universe u v

inductive Term (σ : Nat → Sort u) (X : Sort v) where
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
