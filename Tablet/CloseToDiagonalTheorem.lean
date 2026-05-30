import Tablet.DigraphToGraphIndependentSetBound
import Tablet.F2ForwardIndependentNearDiagonalBound
import Tablet.SamplingKsFreeRamseyBound
import Tablet.SimpleGraphNoIndependentSetFromCountZero

-- [TABLET NODE: CloseToDiagonalTheorem]

theorem CloseToDiagonalTheorem :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧ ∃ s0 : ℕ,
      ∀ s a : ℕ, s0 ≤ s → (a : ℝ) ≤ delta * (s : ℝ) →
        (1 - eps) * ((s : ℝ) / Real.exp 1) *
            Real.rpow 2
              (((s : ℝ) + (a : ℝ) - 1) / 2 -
                ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
          (RamseyNumber s (s + a) : ℝ) := by
-- BODY
  sorry
