import Tablet.LoopGraphAdjacencyAction
import Mathlib.Analysis.InnerProductSpace.PiL2

-- [TABLET NODE: LoopGraphAdjacencyEuclideanOperator]

universe u

noncomputable def LoopGraphAdjacencyEuclideanOperator {V : Type u} [Fintype V]
    (G : LoopGraph V) : EuclideanSpace ℝ V →ₗ[ℝ] EuclideanSpace ℝ V :=
-- BODY
  { toFun := fun x =>
      WithLp.toLp 2 (LoopGraphAdjacencyAction G (fun w : V => x w))
    map_add' := by
      classical
      intro x y
      ext v
      calc
        (∑ w : V, if G v w then (x + y).ofLp w else 0)
            = ∑ w : V,
                ((if G v w then x.ofLp w else 0) +
                  (if G v w then y.ofLp w else 0)) := by
              refine Finset.sum_congr rfl ?_
              intro w hw
              by_cases h : G v w <;> simp [h]
        _ = (∑ w : V, if G v w then x.ofLp w else 0) +
            ∑ w : V, if G v w then y.ofLp w else 0 := by
              rw [Finset.sum_add_distrib]
        _ = (LoopGraphAdjacencyAction G (fun w : V => x.ofLp w) v +
              LoopGraphAdjacencyAction G (fun w : V => y.ofLp w) v) := by
              simp [LoopGraphAdjacencyAction]
    map_smul' := by
      classical
      intro c x
      ext v
      simp [LoopGraphAdjacencyAction, Finset.mul_sum] }
