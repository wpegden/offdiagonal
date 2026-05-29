import Tablet.ForwardIndependentTupleCount
import Tablet.SparseNeighborhoodSetBound

-- [TABLET NODE: ProductDigraphShrinkingSequenceBound]

universe u

theorem ProductDigraphShrinkingSequenceBound {W : Type u} [Fintype W]
    (D : Digraph W) (eta : ℝ) (M t z : ℕ)
    (heta : 0 ≤ eta) :
    ((ForwardIndependentTupleCount D t : ℕ) : ℝ) ≤
      (8 : ℝ) ^ t * Real.rpow eta ((t - z : ℕ) : ℝ) * (M : ℝ) ^ t := by
-- BODY
  sorry
