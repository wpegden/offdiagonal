import Tablet.Preamble

-- [TABLET NODE: MainTheoremLargeKComparison]

theorem MainTheoremLargeKComparison (s k : ℕ) (A B Q eta : ℝ)
    (hs : 4 ≤ s) (hk : 2 ≤ k) (hB_pos : 0 < B)
    (hQ_pos : 0 < Q) (heta_pos : 0 < eta)
    (heta_upper : eta ≤ B / Q)
    (hQ_lower :
      A * ((k : ℝ) ^ (s - 3)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤ Q)
    (habsorb :
      1 ≤ (A / (200 * B)) *
        (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)))) :
    (A / (200 * B)) *
        (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))) ≤
      (k : ℝ) / (100 * eta) - 1 := by
-- BODY
  have hk_pos_nat : 0 < k := by omega
  have hk_gt_one_nat : 1 < k := by omega
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hk_gt_one : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk_gt_one_nat
  have hlog_pos : 0 < Real.log (k : ℝ) := Real.log_pos hk_gt_one
  have hden_pos : 0 < (Real.log (k : ℝ)) ^ (2 * s - 6) := by
    positivity
  have hetaQ_le_B : eta * Q ≤ B := by
    rw [le_div_iff₀ hQ_pos] at heta_upper
    exact heta_upper
  have hQ_div_B_le_eta_inv : Q / B ≤ eta⁻¹ := by
    rw [div_le_iff₀ hB_pos]
    rw [le_inv_mul_iff₀ heta_pos]
    nlinarith [hetaQ_le_B]
  have hcoef_nonneg : 0 ≤ (k : ℝ) / 100 := by positivity
  have hfirst :
      ((k : ℝ) / 100) * (Q / B) ≤ ((k : ℝ) / 100) * eta⁻¹ :=
    mul_le_mul_of_nonneg_left hQ_div_B_le_eta_inv hcoef_nonneg
  have hfirst' :
      (k : ℝ) * Q / (100 * B) ≤ (k : ℝ) / (100 * eta) := by
    calc
      (k : ℝ) * Q / (100 * B)
          = ((k : ℝ) / 100) * (Q / B) := by ring
      _ ≤ ((k : ℝ) / 100) * eta⁻¹ := hfirst
      _ = (k : ℝ) / (100 * eta) := by
        field_simp [ne_of_gt heta_pos]
  have hmult_nonneg : 0 ≤ (k : ℝ) / (100 * B) := by positivity
  have hsecond_raw :
      ((k : ℝ) / (100 * B)) *
          (A * ((k : ℝ) ^ (s - 3)) /
            ((Real.log (k : ℝ)) ^ (2 * s - 6))) ≤
        ((k : ℝ) / (100 * B)) * Q :=
    mul_le_mul_of_nonneg_left hQ_lower hmult_nonneg
  have hpow_succ : (k : ℝ) ^ (s - 2) = (k : ℝ) * (k : ℝ) ^ (s - 3) := by
    have hsub : s - 2 = (s - 3) + 1 := by omega
    rw [hsub, pow_succ]
    ring
  have hsecond :
      (A / (100 * B)) *
          (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))) ≤
        (k : ℝ) * Q / (100 * B) := by
    calc
      (A / (100 * B)) *
          (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)))
          = ((k : ℝ) / (100 * B)) *
              (A * ((k : ℝ) ^ (s - 3)) /
                ((Real.log (k : ℝ)) ^ (2 * s - 6))) := by
            rw [hpow_succ]
            ring
      _ ≤ ((k : ℝ) / (100 * B)) * Q := hsecond_raw
      _ = (k : ℝ) * Q / (100 * B) := by ring
  let T : ℝ := ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))
  let X : ℝ := (A / (200 * B)) * T
  have hdouble :
      (A / (100 * B)) * T = 2 * X := by
    dsimp [X]
    field_simp [ne_of_gt hB_pos]
    ring
  have htarget_to_double : X ≤ (A / (100 * B)) * T - 1 := by
    rw [hdouble]
    nlinarith [habsorb]
  have hdouble_to_ramsey :
      (A / (100 * B)) * T ≤ (k : ℝ) / (100 * eta) := by
    dsimp [T]
    exact hsecond.trans hfirst'
  calc
    (A / (200 * B)) *
        (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)))
        = X := by rfl
    _ ≤ (A / (100 * B)) * T - 1 := htarget_to_double
    _ ≤ (k : ℝ) / (100 * eta) - 1 := by linarith
