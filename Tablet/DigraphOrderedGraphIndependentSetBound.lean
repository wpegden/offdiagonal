import Tablet.DigraphOrderedGraph
import Tablet.ForwardIndependentTupleCount
import Tablet.SimpleGraphIndependentSetCount

-- [TABLET NODE: DigraphOrderedGraphIndependentSetBound]

universe u

theorem DigraphOrderedGraphIndependentSetBound {W : Type u} [Fintype W]
    (D : Digraph W) (k : ℕ) (hk : 1 ≤ k) :
    ∃ r : W → ℕ,
      ((SimpleGraphIndependentSetCount (DigraphOrderedGraph D r) k : ℕ) : ℝ) ≤
        (Real.exp 1 / (k : ℝ)) ^ k *
          ((ForwardIndependentTupleCount D k : ℕ) : ℝ) := by
-- BODY
  sorry
