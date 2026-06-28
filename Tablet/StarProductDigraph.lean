import Tablet.Digraph
import Tablet.ProductDigraphVertex

-- [TABLET NODE: StarProductDigraph]

universe u

def StarProductDigraph {V : Type u} (G : LoopGraph V) :
    Digraph (ProductDigraphVertex G) :=
-- BODY
  fun x y => G x.val.1 y.val.2 ∧ ¬ G y.val.1 x.val.2
