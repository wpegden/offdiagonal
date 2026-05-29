import Tablet.LoopGraphAdjacencyEuclideanInner
import Tablet.LoopGraphAdjacencyActionSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Spectrum

-- [TABLET NODE: LoopGraphAdjacencyEuclideanOperatorSymmetric]

universe u

theorem LoopGraphAdjacencyEuclideanOperatorSymmetric {V : Type u} [Fintype V]
    (G : LoopGraph V) (hGsym : LoopGraphSymmetric G) :
    LinearMap.IsSymmetric (LoopGraphAdjacencyEuclideanOperator G) := by
-- BODY
  intro x y
  calc
    inner ℝ (LoopGraphAdjacencyEuclideanOperator G x) y
        = ∑ v : V, LoopGraphAdjacencyAction G (fun w : V => x w) v * y v := by
          simp [LoopGraphAdjacencyEuclideanOperator]
          simpa [dotProduct, mul_comm] using
            (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ)
              (LoopGraphAdjacencyAction G (fun w : V => x w))
              (fun v : V => y v))
    _ = ∑ v : V, x v * LoopGraphAdjacencyAction G (fun w : V => y w) v := by
          exact (LoopGraphAdjacencyActionSelfAdjoint G hGsym
            (fun w : V => x w) (fun w : V => y w)).symm
    _ = inner ℝ x (LoopGraphAdjacencyEuclideanOperator G y) := by
          rw [LoopGraphAdjacencyEuclideanInner]
