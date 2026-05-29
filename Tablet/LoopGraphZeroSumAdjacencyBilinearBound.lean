import Tablet.LoopGraphNdLambda
import Tablet.LoopGraphAdjacencyActionSelfAdjoint
import Tablet.LoopGraphNdLambdaAdjacencyActionZeroSum
import Tablet.LoopGraphAdjacencyEuclideanInner
import Tablet.LoopGraphZeroSumAdjacencyEuclideanOperator
import Tablet.LoopGraphZeroSumEuclideanEigenvalueBound

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
  have hEuclideanInner :
      inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ V)
        (LoopGraphAdjacencyEuclideanOperator G (WithLp.toLp 2 g)) =
        ∑ v : V, f v * LoopGraphAdjacencyAction G g v :=
    LoopGraphAdjacencyEuclideanInner G f g
  let W := LoopGraphEuclideanZeroSumSubmodule V
  have hf_mem : (WithLp.toLp 2 f : EuclideanSpace ℝ V) ∈ W := by
    simpa [W, LoopGraphEuclideanZeroSumSubmodule] using hf
  have hg_mem : (WithLp.toLp 2 g : EuclideanSpace ℝ V) ∈ W := by
    simpa [W, LoopGraphEuclideanZeroSumSubmodule] using hg
  let fW : W := ⟨(WithLp.toLp 2 f : EuclideanSpace ℝ V), hf_mem⟩
  let gW : W := ⟨(WithLp.toLp 2 g : EuclideanSpace ℝ V), hg_mem⟩
  let TW := LoopGraphZeroSumAdjacencyEuclideanOperator G n d lambda hG
  have hTWg_coe :
      ((TW gW : W) : EuclideanSpace ℝ V) =
        LoopGraphAdjacencyEuclideanOperator G (WithLp.toLp 2 g) := rfl
  have hEuclideanEigenvalueBound :
      ∀ (mu : ℝ) (x : W), x ≠ 0 →
        LoopGraphAdjacencyEuclideanOperator G (x : EuclideanSpace ℝ V) =
          mu • (x : EuclideanSpace ℝ V) → |mu| ≤ lambda := by
    intro mu x hx hEigen
    exact LoopGraphZeroSumEuclideanEigenvalueBound G n d lambda mu hG x hx hEigen
  sorry
