import Tablet.LoopGraph

-- [TABLET NODE: LoopGraphDegree]

universe u

noncomputable def LoopGraphDegree {V : Type u} [Fintype V] (G : LoopGraph V) (v : V) : ℕ := by
-- BODY
  classical
  exact (Finset.univ.filter (fun w => G v w)).card
