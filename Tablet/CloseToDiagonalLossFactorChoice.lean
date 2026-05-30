import Tablet.Preamble

-- [TABLET NODE: CloseToDiagonalLossFactorChoice]

theorem CloseToDiagonalLossFactorChoice (eps : ℝ) (heps : 0 < eps)
    (heps_lt : eps < 1) :
    ∃ rho eta delta1 : ℝ,
      0 < rho ∧ 0 < eta ∧ 0 < delta1 ∧ delta1 ≤ 1 / 2 ∧
        1 - eps / 2 ≤
          (1 - rho) * Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta1)) := by
-- BODY
  refine ⟨eps / 8, eps / 32, eps / 80, ?_, ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · positivity
  · nlinarith
  · have hlog_le_two : Real.log 2 ≤ (2 : ℝ) :=
      Real.log_le_self (by norm_num : (0 : ℝ) ≤ 2)
    have hmul_log : (eps / 16) * Real.log 2 ≤ eps / 8 := by
      have hmul := mul_le_mul_of_nonneg_left hlog_le_two (by positivity : 0 ≤ eps / 16)
      nlinarith
    have hrpow_lower : 1 - eps / 8 ≤ Real.rpow 2 (-(eps / 16)) := by
      change 1 - eps / 8 ≤ (2 : ℝ) ^ (-(eps / 16))
      rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hlin : 1 - eps / 8 ≤ Real.log 2 * (-(eps / 16)) + 1 := by
        nlinarith
      exact hlin.trans (Real.add_one_le_exp _)
    have hfactor_nonneg : 0 ≤ 1 - eps / 8 := by nlinarith
    have hsq_lower : 1 - eps / 2 ≤ (1 - eps / 8) * (1 - eps / 8) := by
      nlinarith [sq_nonneg (eps / 8)]
    have hmul_lower :
        (1 - eps / 8) * (1 - eps / 8) ≤
          (1 - eps / 8) * Real.rpow 2 (-(eps / 16)) :=
      mul_le_mul_of_nonneg_left hrpow_lower hfactor_nonneg
    calc
      1 - eps / 2 ≤ (1 - eps / 8) * (1 - eps / 8) := hsq_lower
      _ ≤ (1 - eps / 8) * Real.rpow 2 (-(eps / 16)) := hmul_lower
      _ = (1 - eps / 8) *
          Real.rpow 2 (-(eps / 32 + (5 / 2 : ℝ) * (eps / 80))) := by
            congr 2
            ring
