import Tablet.Digraph

-- [TABLET NODE: ForwardIndependentTuple]

universe u

def ForwardIndependentTuple {V : Type u} {k : ℕ}
    (D : Digraph V) (v : Fin k → V) : Prop :=
-- BODY
  ∀ i j : Fin k, i < j → ¬ D (v i) (v j)
