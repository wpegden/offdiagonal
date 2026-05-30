import Tablet.CloseToDiagonalExponentComparison

-- [TABLET NODE: CloseToDiagonalPositiveSamplingLowerBound]

theorem CloseToDiagonalPositiveSamplingLowerBound
    (eps rho eta delta delta1 : ℝ) (s a : ℕ)
    (heps : 0 < eps) (heps_lt : eps < 1) (heta : 0 ≤ eta)
    (hdelta_nonneg : 0 ≤ delta) (hdelta_le_delta1 : delta ≤ delta1)
    (hloss : 1 - eps / 2 ≤
      (1 - rho) * Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta1)))
    (hN : (1 - rho) * (((2 ^ (2 * s - 3) : ℕ) : ℝ)) ≤
      ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ))
    (hBlarge :
      2 / eps ≤
        ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))))
    (hs4 : 4 ≤ s) (ha : (a : ℝ) ≤ delta * (s : ℝ)) :
    let E : ℝ := (3 / 2 : ℝ) * (s : ℝ) ^ 2 + (a : ℝ) * (s : ℝ) -
      (5 / 2 : ℝ) * (s : ℝ) + eta * (s : ℝ)
    let p0 : ℝ := (((s + a : ℕ) : ℝ) / Real.exp 1) *
      Real.rpow 2 (-(E / ((s + a : ℕ) : ℝ)))
    (1 - eps) * ((s : ℝ) / Real.exp 1) *
        Real.rpow 2
          ((((s : ℝ) + (a : ℝ) - 1) / 2) -
            ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
      p0 * ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) - 1 := by
-- BODY
  intro E p0
  let T : ℝ := (((s : ℝ) + (a : ℝ) - 1) / 2) -
    ((a : ℝ) ^ 2) / (2 * (s : ℝ))
  let loss : ℝ := (5 / 2 : ℝ) * delta + eta
  let B : ℝ := ((s : ℝ) / Real.exp 1) * Real.rpow 2 T
  let A : ℝ := ((2 ^ (2 * s - 3) : ℕ) : ℝ)
  let N : ℝ := ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ)
  have hspos_nat : 0 < s := by omega
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
  have hkpos_nat : 0 < s + a := by omega
  have hp0_nonneg : 0 ≤ p0 := by
    dsimp [p0, E]
    positivity
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    positivity
  have hloss_factor_pos :
      0 < Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta1)) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hone_minus_rho_pos : 0 < 1 - rho := by
    have hleft_pos : 0 < 1 - eps / 2 := by nlinarith
    by_contra hnot
    have hnonpos : 1 - rho ≤ 0 := le_of_not_gt hnot
    have hprod_nonpos :
        (1 - rho) * Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta1)) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hnonpos hloss_factor_pos.le
    linarith
  have hone_minus_rho_nonneg : 0 ≤ 1 - rho := hone_minus_rho_pos.le
  have hdelta_loss_exp :
      -(eta + (5 / 2 : ℝ) * delta1) ≤ -(eta + (5 / 2 : ℝ) * delta) := by
    nlinarith
  have hdelta_loss_rpow :
      Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta1)) ≤
        Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hdelta_loss_exp
  have hloss_delta :
      1 - eps / 2 ≤ (1 - rho) * Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta)) := by
    exact hloss.trans
      (mul_le_mul_of_nonneg_left hdelta_loss_rpow hone_minus_rho_nonneg)
  have hexponent := CloseToDiagonalExponentComparison s a delta eta hspos heta hdelta_nonneg ha
  have hp0N_lower :
      (1 - rho) * B * Real.rpow 2 (-loss) ≤ p0 * N := by
    have hpow_exp :
        Real.rpow 2 (T - loss) ≤
          Real.rpow 2 (2 * (s : ℝ) - 3 - E / ((s + a : ℕ) : ℝ)) := by
      dsimp [T, loss, E]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent
    have hcoef_s_le_k :
        (s : ℝ) / Real.exp 1 ≤ ((s + a : ℕ) : ℝ) / Real.exp 1 := by
      exact div_le_div_of_nonneg_right (by exact_mod_cast (Nat.le_add_right s a))
        (Real.exp_pos 1).le
    have hmain_le_pA :
        B * Real.rpow 2 (-loss) ≤ p0 * A := by
      have hA_eq : A = Real.rpow 2 (2 * (s : ℝ) - 3) := by
        dsimp [A]
        have hsub : ((2 * s - 3 : ℕ) : ℝ) = 2 * (s : ℝ) - 3 := by
          norm_num [Nat.cast_sub (by omega : 3 ≤ 2 * s)]
        rw [← hsub]
        norm_num
      have hmul_rpow :
          Real.rpow 2 T * Real.rpow 2 (-loss) = Real.rpow 2 (T - loss) := by
        change (2 : ℝ) ^ T * (2 : ℝ) ^ (-loss) = (2 : ℝ) ^ (T - loss)
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
      have hpA_eq :
          p0 * A =
            (((s + a : ℕ) : ℝ) / Real.exp 1) *
              Real.rpow 2 (2 * (s : ℝ) - 3 - E / ((s + a : ℕ) : ℝ)) := by
        dsimp [p0]
        rw [hA_eq]
        change (((s + a : ℕ) : ℝ) / Real.exp 1) *
            (2 : ℝ) ^ (-(E / ((s + a : ℕ) : ℝ))) *
              (2 : ℝ) ^ (2 * (s : ℝ) - 3) =
          (((s + a : ℕ) : ℝ) / Real.exp 1) *
            (2 : ℝ) ^ (2 * (s : ℝ) - 3 - E / ((s + a : ℕ) : ℝ))
        rw [mul_assoc]
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
        ring_nf
      calc
        B * Real.rpow 2 (-loss)
            = ((s : ℝ) / Real.exp 1) * Real.rpow 2 (T - loss) := by
              dsimp [B]
              change (s : ℝ) / Real.exp 1 * Real.rpow 2 T *
                  Real.rpow 2 (-loss) =
                (s : ℝ) / Real.exp 1 * Real.rpow 2 (T - loss)
              rw [mul_assoc, hmul_rpow]
        _ ≤ (((s + a : ℕ) : ℝ) / Real.exp 1) *
              Real.rpow 2 (2 * (s : ℝ) - 3 - E / ((s + a : ℕ) : ℝ)) := by
              exact mul_le_mul hcoef_s_le_k hpow_exp
                (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
                (div_nonneg (by positivity) (Real.exp_pos 1).le)
        _ = p0 * A := hpA_eq.symm
    calc
      (1 - rho) * B * Real.rpow 2 (-loss)
          ≤ (1 - rho) * (p0 * A) := by
            simpa [mul_assoc] using
              mul_le_mul_of_nonneg_left hmain_le_pA hone_minus_rho_nonneg
      _ = p0 * ((1 - rho) * A) := by ring
      _ ≤ p0 * N := by
            exact mul_le_mul_of_nonneg_left (by simpa [A, N] using hN) hp0_nonneg
  have hlossB :
      (1 - eps / 2) * B ≤ (1 - rho) * B * Real.rpow 2 (-loss) := by
    have htmp := mul_le_mul_of_nonneg_right hloss_delta hB_nonneg
    calc
      (1 - eps / 2) * B ≤
          ((1 - rho) * Real.rpow 2 (-(eta + (5 / 2 : ℝ) * delta))) * B := htmp
      _ = (1 - rho) * B * Real.rpow 2 (-loss) := by
          dsimp [loss]
          ring_nf
  have hhalfB_le_pN : (1 - eps / 2) * B ≤ p0 * N :=
    hlossB.trans hp0N_lower
  have hone_le_epsB_half : 1 ≤ eps / 2 * B := by
    have hmul := mul_le_mul_of_nonneg_left (by simpa [B, T] using hBlarge)
      (by positivity : 0 ≤ eps / 2)
    calc
      1 = (eps / 2) * (2 / eps) := by field_simp [heps.ne']
      _ ≤ eps / 2 * B := hmul
  have htarget_absorb : (1 - eps) * B ≤ (1 - eps / 2) * B - 1 := by
    nlinarith
  calc
    (1 - eps) * ((s : ℝ) / Real.exp 1) *
        Real.rpow 2
          ((((s : ℝ) + (a : ℝ) - 1) / 2) -
            ((a : ℝ) ^ 2) / (2 * (s : ℝ)))
        = (1 - eps) * B := by simp [B, T, mul_assoc]
    _ ≤ (1 - eps / 2) * B - 1 := htarget_absorb
    _ ≤ p0 * N - 1 := by linarith
