import Tablet.LoopGraph

-- [TABLET NODE: LoopGraphEdgeCountBetween]

universe u

noncomputable def LoopGraphEdgeCountBetween {V : Type u}
    (G : LoopGraph V) (A B : Finset V) : ℕ := by
-- BODY
  classical
  exact ((A.product B).filter (fun p => G p.1 p.2)).card
