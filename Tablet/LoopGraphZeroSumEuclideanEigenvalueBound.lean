import Tablet.LoopGraphZeroSumEuclideanEigenpairNonprincipal
import Tablet.LoopGraphNdLambda

-- [TABLET NODE: LoopGraphZeroSumEuclideanEigenvalueBound]

universe u

theorem LoopGraphZeroSumEuclideanEigenvalueBound {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda mu : ℝ)
    (hG : LoopGraphNdLambda G n d lambda)
    (x : LoopGraphEuclideanZeroSumSubmodule V)
    (hx : x ≠ 0)
    (hEigen :
      LoopGraphAdjacencyEuclideanOperator G (x : EuclideanSpace ℝ V) =
        mu • (x : EuclideanSpace ℝ V)) :
    |mu| ≤ lambda := by
-- BODY
  exact hG.2.2.2.1 mu
    (LoopGraphZeroSumEuclideanEigenpairNonprincipal G mu x hx hEigen)
