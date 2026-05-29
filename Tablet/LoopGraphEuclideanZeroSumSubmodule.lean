import Tablet.LoopGraphAdjacencyEuclideanOperator

-- [TABLET NODE: LoopGraphEuclideanZeroSumSubmodule]

universe u

noncomputable def LoopGraphEuclideanZeroSumSubmodule (V : Type u) [Fintype V] :
    Submodule ℝ (EuclideanSpace ℝ V) :=
-- BODY
  { carrier := {x | (∑ v : V, x v) = 0}
    zero_mem' := by
      simp
    add_mem' := by
      intro x y hx hy
      calc
        (∑ v : V, (x + y) v) = ∑ v : V, (x v + y v) := by
          simp
        _ = (∑ v : V, x v) + ∑ v : V, y v := by
          rw [Finset.sum_add_distrib]
        _ = 0 := by
          rw [hx, hy, zero_add]
    smul_mem' := by
      intro c x hx
      calc
        (∑ v : V, (c • x) v) = ∑ v : V, c * x v := by
          simp
        _ = c * ∑ v : V, x v := by
          rw [Finset.mul_sum]
        _ = 0 := by
          rw [hx, mul_zero] }
