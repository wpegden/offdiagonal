import Tablet.LoopGraphAdjacencyActionSelfAdjoint
import Tablet.LoopGraphNdLambdaAdjacencyOne

-- [TABLET NODE: LoopGraphNdLambdaAdjacencyActionZeroSum]

universe u

theorem LoopGraphNdLambdaAdjacencyActionZeroSum {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) (f : V → ℝ)
    (hf : (∑ v : V, f v) = 0) :
    (∑ v : V, LoopGraphAdjacencyAction G f v) = 0 := by
-- BODY
  classical
  have hself :=
    LoopGraphAdjacencyActionSelfAdjoint G hG.2.1 (fun _ : V => (1 : ℝ)) f
  have hone :
      (∑ v : V, LoopGraphAdjacencyAction G (fun _ : V => (1 : ℝ)) v * f v) =
        ∑ v : V, (d : ℝ) * f v := by
    refine Finset.sum_congr rfl ?_
    intro v hv
    rw [LoopGraphNdLambdaAdjacencyOne G n d lambda hG v]
  calc
    (∑ v : V, LoopGraphAdjacencyAction G f v)
        = ∑ v : V, (1 : ℝ) * LoopGraphAdjacencyAction G f v := by simp
    _ = ∑ v : V, LoopGraphAdjacencyAction G (fun _ : V => (1 : ℝ)) v * f v := hself
    _ = ∑ v : V, (d : ℝ) * f v := hone
    _ = (d : ℝ) * ∑ v : V, f v := by rw [Finset.mul_sum]
    _ = 0 := by rw [hf, mul_zero]
