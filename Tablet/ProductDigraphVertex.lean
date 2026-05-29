import Tablet.LoopGraph

-- [TABLET NODE: ProductDigraphVertex]

universe u

abbrev ProductDigraphVertex {V : Type u} (F : LoopGraph V) :=
-- BODY
  {p : V × V // F p.1 p.2}
