import Mathlib.Tactic
import Tablet.StarProductRankAtMostCardLeSuccMulLayerChoice

-- [TABLET NODE: StarProductLayerChoiceRealLowerBound]

universe u

theorem StarProductLayerChoiceRealLowerBound (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ) :
    ((StarProductRankAtMostSet K t p r).card : ℝ) / ((r + 1 : ℕ) : ℝ) ≤
      ((StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card : ℝ) := by
-- BODY
  have hnat := StarProductRankAtMostCardLeSuccMulLayerChoice K t p r
  have hcast :
      ((StarProductRankAtMostSet K t p r).card : ℝ) ≤
        ((r + 1 : ℕ) : ℝ) *
          ((StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card : ℝ) := by
    exact_mod_cast hnat
  have hpos : (0 : ℝ) < ((r + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_pos r
  rw [div_le_iff₀ hpos]
  nlinarith
