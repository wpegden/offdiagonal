import Tablet.MulticolorRamseyNumber
import Tablet.RandomHomomorphismColoringBound

-- [TABLET NODE: MulticolorTheorem]

theorem MulticolorTheorem :
    ∀ ell : ℕ, 3 ≤ ell → ∃ c : ℝ, 0 < c ∧ ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      c * Real.rpow 2 ((((ell - 1) * s : ℕ) : ℝ) / 2) ≤
        (MulticolorRamseyNumber s ell : ℝ) := by
-- BODY
  sorry
