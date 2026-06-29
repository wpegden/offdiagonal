import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductQPowerLeTwoPow]

theorem StarProductQPowerLeTwoPow (A C : ℝ) (t q k w : ℕ)
    (hA_nonneg : 0 ≤ A)
    (hscale : 2 * (t : ℝ) * A ≤ C * Real.log 2)
    (hq : 2 ≤ q)
    (hw : (w : ℝ) ≤ A * (q : ℝ) * Real.log (q : ℝ))
    (hk : C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ)) :
    (q : ℝ) ^ (2 * t * w) ≤ (2 : ℝ) ^ k := by
-- BODY
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hq)
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (le_trans (by norm_num : 1 ≤ 2) hq)
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq_ge_one
  have hC_nonneg : 0 ≤ C := by nlinarith
  have hleft_le :
      (2 * (t : ℝ) * (w : ℝ)) * Real.log (q : ℝ) ≤
        (2 * (t : ℝ) * A) * ((q : ℝ) * (Real.log (q : ℝ)) ^ 2) := by
    have hcoef : 0 ≤ 2 * (t : ℝ) * Real.log (q : ℝ) := by positivity
    have hmul := mul_le_mul_of_nonneg_left hw hcoef
    nlinarith
  have hmiddle_le :
      (2 * (t : ℝ) * A) * ((q : ℝ) * (Real.log (q : ℝ)) ^ 2) ≤
        (C * Real.log 2) * ((q : ℝ) * (Real.log (q : ℝ)) ^ 2) := by
    have hnonneg : 0 ≤ (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by positivity
    exact mul_le_mul_of_nonneg_right hscale hnonneg
  have hright_le :
      (C * Real.log 2) * ((q : ℝ) * (Real.log (q : ℝ)) ^ 2) ≤
        (k : ℝ) * Real.log 2 := by
    have hmul := mul_le_mul_of_nonneg_right hk hlog2_pos.le
    nlinarith
  have hlog_bound :
      ((2 * t * w : ℕ) : ℝ) * Real.log (q : ℝ) ≤ (k : ℝ) * Real.log 2 := by
    have htw_cast : ((2 * t * w : ℕ) : ℝ) = 2 * (t : ℝ) * (w : ℝ) := by norm_num
    rw [htw_cast]
    exact hleft_le.trans (hmiddle_le.trans hright_le)
  apply Real.le_pow_of_log_le (by norm_num : (0 : ℝ) < 2)
  rw [Real.log_pow]
  exact hlog_bound
