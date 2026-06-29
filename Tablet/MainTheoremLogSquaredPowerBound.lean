import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Tablet.Preamble

-- [TABLET NODE: MainTheoremLogSquaredPowerBound]

open Filter

theorem MainTheoremLogSquaredPowerBound :
    ∃ Q0 : ℝ, ∀ q : ℕ, Q0 ≤ (q : ℝ) →
      4 * (Real.log (q : ℝ)) ^ 2 ≤ Real.exp 1 * (q : ℝ) := by
-- BODY
  have hcoef : (0 : ℝ) < Real.exp 1 / 4 := by positivity
  have hsmall :
      ∀ᶠ x : ℝ in atTop,
        ‖(Real.log x) ^ 2‖ ≤ (Real.exp 1 / 4 : ℝ) * ‖id x‖ := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).def hcoef
  rcases eventually_atTop.1 hsmall with ⟨Q0, hQ0⟩
  refine ⟨Q0, ?_⟩
  intro q hq
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hlogsq_nonneg : 0 ≤ (Real.log (q : ℝ)) ^ 2 := sq_nonneg _
  have hbound :
      (Real.log (q : ℝ)) ^ 2 ≤ (Real.exp 1 / 4 : ℝ) * (q : ℝ) := by
    simpa [Real.norm_of_nonneg hlogsq_nonneg,
      Real.norm_of_nonneg hq_nonneg, id] using hQ0 (q : ℝ) hq
  calc
    4 * (Real.log (q : ℝ)) ^ 2
        ≤ 4 * ((Real.exp 1 / 4 : ℝ) * (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hbound (by norm_num)
    _ = Real.exp 1 * (q : ℝ) := by ring

