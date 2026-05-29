import Tablet.LoopGraphNdLambda
import Tablet.LoopGraphAdjacencyActionSelfAdjoint
import Tablet.LoopGraphNdLambdaAdjacencyActionZeroSum

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
  have hSelfAdjoint :
      (∑ v : V, f v * LoopGraphAdjacencyAction G g v) =
        ∑ v : V, LoopGraphAdjacencyAction G f v * g v :=
    LoopGraphAdjacencyActionSelfAdjoint G hG.2.1 f g
  have hf_invariant :
      (∑ v : V, LoopGraphAdjacencyAction G f v) = 0 :=
    LoopGraphNdLambdaAdjacencyActionZeroSum G n d lambda hG f hf
  have hg_invariant :
      (∑ v : V, LoopGraphAdjacencyAction G g v) = 0 :=
    LoopGraphNdLambdaAdjacencyActionZeroSum G n d lambda hG g hg
  sorry
