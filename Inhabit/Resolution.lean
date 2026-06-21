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
