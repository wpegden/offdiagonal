import Tablet.ComplementPolarityPairHsFree
import Tablet.PolarityGraphParameters
import Tablet.RamseyFromGraphPair

-- [TABLET NODE: OffDiagonalGeneralTheorem]

theorem OffDiagonalGeneralTheorem :
    ∀ delta : ℝ, 0 < delta → ∃ L : ℕ, ∀ s k : ℕ, L ≤ s → L * s ≤ k →
      Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta) * (s : ℝ)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  sorry
