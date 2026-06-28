import Tablet.DigraphToGraphIndependentSetBound
import Tablet.PolarityGraphParameters
import Tablet.ProductDigraphVertexCard
import Tablet.RamseyNumber
import Tablet.SamplingKsFreeRamseyBound
import Tablet.StarProductDigraph
import Tablet.StarProductDigraphTransitiveFree
import Tablet.StarProductForwardIndependentBound

-- [TABLET NODE: MainTheorem]

theorem MainTheorem :
    ∀ s : ℕ, 3 ≤ s → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      c * ((k : ℝ) ^ (s - 1)) / ((Real.log (k : ℝ)) ^ (2 * s - 4)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  sorry
