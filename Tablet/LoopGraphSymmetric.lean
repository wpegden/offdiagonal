import Tablet.LoopGraph

-- [TABLET NODE: LoopGraphSymmetric]

universe u

def LoopGraphSymmetric {V : Type u} (G : LoopGraph V) : Prop :=
-- BODY
  Symmetric G
