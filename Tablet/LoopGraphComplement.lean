import Tablet.LoopGraph

-- [TABLET NODE: LoopGraphComplement]

universe u

def LoopGraphComplement {V : Type u} (G : LoopGraph V) : LoopGraph V :=
-- BODY
  fun x y => ¬ G x y
