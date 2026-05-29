import Tablet.LoopGraphAdjacencyEuclideanOperatorMapsZeroSum
import Tablet.LoopGraphEuclideanZeroSumSubmodule
import Tablet.LoopGraphNdLambda

-- [TABLET NODE: LoopGraphZeroSumAdjacencyEuclideanOperator]

universe u

noncomputable def LoopGraphZeroSumAdjacencyEuclideanOperator {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) :
    LoopGraphEuclideanZeroSumSubmodule V →ₗ[ℝ]
      LoopGraphEuclideanZeroSumSubmodule V :=
-- BODY
  { toFun := fun x =>
      ⟨LoopGraphAdjacencyEuclideanOperator G x,
        by
          classical
          change (∑ v : V, (LoopGraphAdjacencyEuclideanOperator G x) v) = 0
          have hxsum : (∑ v : V, (x : EuclideanSpace ℝ V) v) = 0 := by
            exact x.property
          calc
            (∑ v : V, (LoopGraphAdjacencyEuclideanOperator G x) v)
                = ∑ v : V,
                    LoopGraphAdjacencyAction G (fun w : V => (x : EuclideanSpace ℝ V) w) v := by
                  simp [LoopGraphAdjacencyEuclideanOperator]
            _ = ∑ w : V, (d : ℝ) * (x : EuclideanSpace ℝ V) w := by
                  calc
                    (∑ v : V,
                        LoopGraphAdjacencyAction G
                          (fun w : V => (x : EuclideanSpace ℝ V) w) v)
                        = ∑ v : V, ∑ w : V,
                            if G v w then (x : EuclideanSpace ℝ V) w else 0 := by
                          simp [LoopGraphAdjacencyAction]
                    _ = ∑ w : V, ∑ v : V,
                        if G v w then (x : EuclideanSpace ℝ V) w else 0 := by
                          rw [Finset.sum_comm]
                    _ = ∑ w : V, ∑ v : V,
                        if G w v then (x : EuclideanSpace ℝ V) w else 0 := by
                          refine Finset.sum_congr rfl ?_
                          intro w hw
                          refine Finset.sum_congr rfl ?_
                          intro v hv
                          by_cases hvw : G v w
                          · have hwv : G w v := hG.2.1 hvw
                            simp [hvw, hwv]
                          · have hnot : ¬ G w v := by
                              intro hwv
                              exact hvw (hG.2.1 hwv)
                            simp [hvw, hnot]
                    _ = ∑ w : V, (x : EuclideanSpace ℝ V) w *
                        (∑ v : V, if G w v then (1 : ℝ) else 0) := by
                          refine Finset.sum_congr rfl ?_
                          intro w hw
                          rw [Finset.mul_sum]
                          refine Finset.sum_congr rfl ?_
                          intro v hv
                          by_cases hwv : G w v <;> simp [hwv]
                    _ = ∑ w : V, (x : EuclideanSpace ℝ V) w * (d : ℝ) := by
                          refine Finset.sum_congr rfl ?_
                          intro w hw
                          rw [← hG.2.2.1 w]
                          simp [LoopGraphDegree]
                    _ = ∑ w : V, (d : ℝ) * (x : EuclideanSpace ℝ V) w := by
                          refine Finset.sum_congr rfl ?_
                          intro w hw
                          ring
            _ = (d : ℝ) * ∑ w : V, (x : EuclideanSpace ℝ V) w := by
                  rw [Finset.mul_sum]
            _ = 0 := by
                  rw [hxsum, mul_zero]⟩
    map_add' := by
      intro x y
      ext v
      simp
    map_smul' := by
      intro c x
      ext v
      simp }
