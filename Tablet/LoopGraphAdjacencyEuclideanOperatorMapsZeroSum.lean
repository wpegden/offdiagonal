import Tablet.LoopGraphEuclideanZeroSumSubmodule
import Tablet.LoopGraphNdLambdaAdjacencyActionZeroSum

-- [TABLET NODE: LoopGraphAdjacencyEuclideanOperatorMapsZeroSum]

universe u

theorem LoopGraphAdjacencyEuclideanOperatorMapsZeroSum {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) :
    ∀ x ∈ LoopGraphEuclideanZeroSumSubmodule V,
      LoopGraphAdjacencyEuclideanOperator G x ∈ LoopGraphEuclideanZeroSumSubmodule V := by
-- BODY
  intro x hx
  have hxsum : (∑ v : V, (fun w : V => x w) v) = 0 := by
    simpa [LoopGraphEuclideanZeroSumSubmodule] using hx
  simpa [LoopGraphEuclideanZeroSumSubmodule, LoopGraphAdjacencyEuclideanOperator] using
    (LoopGraphNdLambdaAdjacencyActionZeroSum G n d lambda hG (fun w : V => x w) hxsum)
