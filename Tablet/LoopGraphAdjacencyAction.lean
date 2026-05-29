import Tablet.LoopGraph

-- [TABLET NODE: LoopGraphAdjacencyAction]

universe u

noncomputable def LoopGraphAdjacencyAction {V : Type u} [Fintype V]
    (G : LoopGraph V) (f : V → ℝ) (v : V) : ℝ := by
-- BODY
  classical
  exact Finset.univ.sum (fun w => if G v w then f w else 0)
