import Tablet.Preamble
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Log.Base

-- [TABLET NODE: F2NearDiagonalBinomialLogBound]

theorem F2NearDiagonalBinomialLogBound (n m b : ℕ) (hnpos : 0 < n) (hmpos : 0 < m)
    (hbpos : 0 < b) (hbm : b ≤ m) :
    ((Nat.choose n m : ℕ) : ℝ) ≤
      Real.rpow 2 ((m : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (b : ℝ))) := by
-- BODY
  have hnnonneg : 0 ≤ (n : ℝ) := by exact_mod_cast hnpos.le
  have hmpos_real : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hbpos_real : 0 < (b : ℝ) := by exact_mod_cast hbpos
  have hmfac_pos : 0 < (m.factorial : ℝ) := by positivity
  have hchoose_div :
      ((Nat.choose n m : ℕ) : ℝ) ≤ (n : ℝ) ^ m / (m.factorial : ℝ) :=
    Nat.choose_le_pow_div (α := ℝ) m n
  have hfact_exp : (m : ℝ) ^ m / (m.factorial : ℝ) ≤ Real.exp (m : ℝ) :=
    Real.pow_div_factorial_le_exp (m : ℝ) (by positivity) m
  have h_inv_fact :
      (1 : ℝ) / (m.factorial : ℝ) ≤ Real.exp (m : ℝ) / (m : ℝ) ^ m := by
    have hpow_pos : 0 < (m : ℝ) ^ m := pow_pos hmpos_real m
    calc
      (1 : ℝ) / (m.factorial : ℝ) =
          ((m : ℝ) ^ m / (m.factorial : ℝ)) / (m : ℝ) ^ m := by
            field_simp [hmfac_pos.ne', hpow_pos.ne']
      _ ≤ Real.exp (m : ℝ) / (m : ℝ) ^ m :=
          div_le_div_of_nonneg_right hfact_exp hpow_pos.le
  have hnm_nonneg : 0 ≤ (n : ℝ) ^ m := pow_nonneg hnnonneg m
  have hchoose_m :
      ((Nat.choose n m : ℕ) : ℝ) ≤
        (n : ℝ) ^ m * (Real.exp (m : ℝ) / (m : ℝ) ^ m) := by
    calc
      ((Nat.choose n m : ℕ) : ℝ) ≤ (n : ℝ) ^ m / (m.factorial : ℝ) := hchoose_div
      _ = (n : ℝ) ^ m * ((1 : ℝ) / (m.factorial : ℝ)) := by ring
      _ ≤ (n : ℝ) ^ m * (Real.exp (m : ℝ) / (m : ℝ) ^ m) :=
        mul_le_mul_of_nonneg_left h_inv_fact hnm_nonneg
  have hbase_m_le_b :
      (n : ℝ) ^ m * (Real.exp (m : ℝ) / (m : ℝ) ^ m) ≤
        (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ m := by
    have hexp_pow : Real.exp (m : ℝ) = (Real.exp 1) ^ m := by
      rw [← Real.exp_nat_mul]
      norm_num
    rw [hexp_pow]
    have hbm_real : (b : ℝ) ≤ (m : ℝ) := by exact_mod_cast hbm
    have hdiv_le : (1 : ℝ) / (m : ℝ) ≤ 1 / (b : ℝ) := by
      exact one_div_le_one_div_of_le hbpos_real hbm_real
    have hbase_le : (Real.exp 1 * (n : ℝ) / (m : ℝ)) ≤
        (Real.exp 1 * (n : ℝ) / (b : ℝ)) := by
      have hnonneg : 0 ≤ Real.exp 1 * (n : ℝ) := by positivity
      calc
        Real.exp 1 * (n : ℝ) / (m : ℝ) = (Real.exp 1 * (n : ℝ)) * (1 / (m : ℝ)) := by ring
        _ ≤ (Real.exp 1 * (n : ℝ)) * (1 / (b : ℝ)) :=
          mul_le_mul_of_nonneg_left hdiv_le hnonneg
        _ = Real.exp 1 * (n : ℝ) / (b : ℝ) := by ring
    have hleft_eq :
        (n : ℝ) ^ m * ((Real.exp 1) ^ m / (m : ℝ) ^ m) =
          (Real.exp 1 * (n : ℝ) / (m : ℝ)) ^ m := by
      rw [div_pow, mul_pow]
      ring
    rw [hleft_eq]
    exact pow_le_pow_left₀ (by positivity) hbase_le m
  have hchoose_rpow :
      ((Nat.choose n m : ℕ) : ℝ) ≤
        (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ m :=
    hchoose_m.trans hbase_m_le_b
  have hbase_pos : 0 < Real.exp 1 * (n : ℝ) / (b : ℝ) := by positivity
  have hlog_identity :
      Real.rpow 2 ((m : ℝ) * Real.logb 2 (Real.exp 1 * (n : ℝ) / (b : ℝ))) =
        (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ m := by
    rw [mul_comm]
    change (2 : ℝ) ^ (Real.logb 2 (Real.exp 1 * (n : ℝ) / (b : ℝ)) * (m : ℝ)) =
      (Real.exp 1 * (n : ℝ) / (b : ℝ)) ^ m
    rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1) hbase_pos]
    rw [Real.rpow_natCast]
  rw [hlog_identity]
  exact hchoose_rpow
