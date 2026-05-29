import Tablet.Digraph

-- [TABLET NODE: DigraphLoopless]

universe u

def DigraphLoopless {V : Type u} (D : Digraph V) : Prop :=
-- BODY
  ∀ v : V, ¬ D v v
