import Tablet.LoopGraphAdjacencyAction
import Tablet.LoopGraphNdLambda

-- [TABLET NODE: LoopGraphNdLambdaAdjacencyOne]

universe u

theorem LoopGraphNdLambdaAdjacencyOne {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) (v : V) :
    LoopGraphAdjacencyAction G (fun _ : V => (1 : ℝ)) v = (d : ℝ) := by
-- BODY
  classical
  rw [← hG.2.2.1 v]
  simp [LoopGraphAdjacencyAction, LoopGraphDegree]
