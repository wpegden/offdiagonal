import Tablet.LoopGraphEuclideanZeroSumSubmodule
import Tablet.LoopGraphNonprincipalEigenvalue

-- [TABLET NODE: LoopGraphZeroSumEuclideanEigenpairNonprincipal]

universe u

theorem LoopGraphZeroSumEuclideanEigenpairNonprincipal {V : Type u} [Fintype V]
    (G : LoopGraph V) (mu : ℝ)
    (x : LoopGraphEuclideanZeroSumSubmodule V)
    (hx : x ≠ 0)
    (hEigen :
      LoopGraphAdjacencyEuclideanOperator G (x : EuclideanSpace ℝ V) =
        mu • (x : EuclideanSpace ℝ V)) :
    LoopGraphNonprincipalEigenvalue G mu := by
-- BODY
  refine ⟨(fun v : V => (x : EuclideanSpace ℝ V) v), ?_, ?_, ?_⟩
  · by_contra hnone
    apply hx
    ext v
    by_contra hv
    exact hnone ⟨v, hv⟩
  · change (∑ v : V, (x : EuclideanSpace ℝ V) v) = 0
    exact x.property
  · intro v
    have hCoord := congrArg (fun y : EuclideanSpace ℝ V => y v) hEigen
    simpa [LoopGraphAdjacencyEuclideanOperator] using hCoord
