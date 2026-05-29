import Tablet.Preamble

-- [TABLET NODE: LoopGraph]

universe u

abbrev LoopGraph (V : Type u) :=
-- BODY
  V → V → Prop
