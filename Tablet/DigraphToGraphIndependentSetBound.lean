import Tablet.ForwardIndependentTupleCount
import Tablet.SimpleGraphIndependentSetCount
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: DigraphToGraphIndependentSetBound]

universe u

theorem DigraphToGraphIndependentSetBound {W : Type u} [Fintype W]
    (D : Digraph W) (s k : ℕ)
    (hD : TransitiveTournamentFree D s) (hk : 1 ≤ k) :
    ∃ G : SimpleGraph W,
      (¬ ∃ S : Finset W, G.IsNClique s S) ∧
        ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) ≤
          (Real.exp 1 / (k : ℝ)) ^ k *
            ((ForwardIndependentTupleCount D k : ℕ) : ℝ) := by
-- BODY
  sorry
