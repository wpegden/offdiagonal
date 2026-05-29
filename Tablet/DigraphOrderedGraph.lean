import Tablet.Digraph

-- [TABLET NODE: DigraphOrderedGraph]

universe u

def DigraphOrderedGraph {V : Type u} (D : Digraph V) (r : V → ℕ) : SimpleGraph V :=
-- BODY
{ Adj := fun u v => (r u < r v ∧ D u v) ∨ (r v < r u ∧ D v u)
  symm := by
    intro u v h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := by
    constructor
    intro u h
    rcases h with h | h
    · exact (lt_irrefl (r u)) h.1
    · exact (lt_irrefl (r u)) h.1 }
