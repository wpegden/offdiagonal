import Tablet.LoopGraphNdLambda

-- [TABLET NODE: LoopGraphZeroSumAdjacencyBilinearBound]

universe u

theorem LoopGraphZeroSumAdjacencyBilinearBound {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda)
    (f g : V → ℝ)
    (hf : (∑ v : V, f v) = 0)
    (hg : (∑ v : V, g v) = 0) :
    |(∑ v : V, f v * LoopGraphAdjacencyAction G g v)| ≤
      lambda * (Real.sqrt (∑ v : V, f v ^ 2) *
        Real.sqrt (∑ v : V, g v ^ 2)) := by
-- BODY
  sorry
