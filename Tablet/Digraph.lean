import Tablet.Preamble

-- [TABLET NODE: Digraph]

universe u

abbrev Digraph (V : Type u) :=
-- BODY
  V → V → Prop
