import Tablet.Digraph
import Tablet.ProductDigraphVertex

-- [TABLET NODE: ProductDigraph]

universe u

def ProductDigraph {V : Type u} (F G : LoopGraph V) :
    Digraph (ProductDigraphVertex F) :=
-- BODY
  fun x y => G x.val.1 y.val.2
