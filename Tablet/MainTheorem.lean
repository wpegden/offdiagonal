import Tablet.ComplementPolarityPairHsFree
import Tablet.PolarityGraphParameters
import Tablet.RamseyFromGraphPair

-- [TABLET NODE: MainTheorem]

theorem MainTheorem :
    ∀ s : ℕ, 4 ≤ s → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      c * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  sorry
