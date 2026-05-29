import Tablet.DigraphToGraphIndependentSetBound
import Tablet.F2ForwardIndependentLinearBound
import Tablet.SamplingKsFreeRamseyBound

-- [TABLET NODE: LinearOffDiagonalTheorem]

theorem LinearOffDiagonalTheorem :
    ∀ C : ℝ, 1 < C → ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) ≤
        (RamseyNumber s (Nat.ceil (C * (s : ℝ))) : ℝ) := by
-- BODY
  sorry
