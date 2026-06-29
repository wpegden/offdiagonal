import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductWLeK]

theorem StarProductWLeK (A C : ℝ) (q k w : ℕ)
    (hA_nonneg : 0 ≤ A)
    (hA_le_C : A ≤ C)
    (hlog_ge_one : 1 ≤ Real.log (q : ℝ))
    (hw : (w : ℝ) ≤ A * (q : ℝ) * Real.log (q : ℝ))
    (hk : C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ)) :
    w ≤ k := by
-- BODY
  have hC_nonneg : 0 ≤ C := le_trans hA_nonneg hA_le_C
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hlog_nonneg : 0 ≤ Real.log (q : ℝ) := le_trans zero_le_one hlog_ge_one
  have hAqlog_le_Cqlog :
      A * (q : ℝ) * Real.log (q : ℝ) ≤
        C * (q : ℝ) * Real.log (q : ℝ) := by
    calc
      A * (q : ℝ) * Real.log (q : ℝ)
          = A * ((q : ℝ) * Real.log (q : ℝ)) := by ring
      _ ≤ C * ((q : ℝ) * Real.log (q : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hA_le_C (mul_nonneg hq_nonneg hlog_nonneg)
      _ = C * (q : ℝ) * Real.log (q : ℝ) := by ring
  have hCqlog_le_Cqlog2 :
      C * (q : ℝ) * Real.log (q : ℝ) ≤
        C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
    have hlog_le_sq :
        Real.log (q : ℝ) ≤ (Real.log (q : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (q : ℝ) - 1)]
    calc
      C * (q : ℝ) * Real.log (q : ℝ)
          = (C * (q : ℝ)) * Real.log (q : ℝ) := by ring
      _ ≤ (C * (q : ℝ)) * (Real.log (q : ℝ)) ^ 2 := by
        exact mul_le_mul_of_nonneg_left hlog_le_sq (mul_nonneg hC_nonneg hq_nonneg)
      _ = C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by ring
  have hw_real : (w : ℝ) ≤ (k : ℝ) :=
    hw.trans (hAqlog_le_Cqlog.trans (hCqlog_le_Cqlog2.trans hk))
  exact_mod_cast hw_real
