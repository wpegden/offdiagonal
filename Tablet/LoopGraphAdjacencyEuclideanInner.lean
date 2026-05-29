import Tablet.LoopGraphAdjacencyEuclideanOperator

-- [TABLET NODE: LoopGraphAdjacencyEuclideanInner]

universe u

theorem LoopGraphAdjacencyEuclideanInner {V : Type u} [Fintype V]
    (G : LoopGraph V) (f g : V → ℝ) :
    inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ V)
      (LoopGraphAdjacencyEuclideanOperator G (WithLp.toLp 2 g)) =
      ∑ v : V, f v * LoopGraphAdjacencyAction G g v := by
-- BODY
  classical
  simp [LoopGraphAdjacencyEuclideanOperator]
  simpa [dotProduct, mul_comm] using
    (EuclideanSpace.inner_toLp_toLp (𝕜 := ℝ) f (LoopGraphAdjacencyAction G g))
