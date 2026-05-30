import Tablet.CloseToDiagonalVertexCountLowerBound

-- [TABLET NODE: LinearOffDiagonalSamplingLowerBound]

open Filter in
theorem LinearOffDiagonalSamplingLowerBound (C : ℝ) (hC : 1 < C) :
    ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      let k : ℕ := Nat.ceil (C * (s : ℝ))
      let E : ℝ := (s : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2
      let p0 : ℝ := ((k : ℝ) / Real.exp 1) * Real.rpow 2 (-(E / (k : ℝ)))
      Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) ≤
        p0 *
            ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) -
          1 := by
-- BODY
  have hCpos : 0 < C := lt_trans (by norm_num) hC
  have h2Cpos : 0 < 2 * C := by positivity
  rcases CloseToDiagonalVertexCountLowerBound (1 / 2 : ℝ) (by norm_num) with
    ⟨sN, _hsN4, hN⟩
  rcases exists_nat_gt (32 * Real.exp 1) with ⟨sCoeff, hsCoeff⟩
  refine ⟨max sN (max sCoeff 8), ?_⟩
  intro s hs k E p0
  let alpha : ℝ := (1 - 1 / (2 * C)) * (s : ℝ)
  let target : ℝ := Real.rpow 2 alpha
  let A : ℝ := ((2 ^ (2 * s - 3) : ℕ) : ℝ)
  let N : ℝ := ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ)
  have hsN : sN ≤ s := le_trans (Nat.le_max_left sN (max sCoeff 8)) hs
  have hsCoeff' : sCoeff ≤ s := by
    exact le_trans (le_trans (Nat.le_max_left sCoeff 8) (Nat.le_max_right sN (max sCoeff 8))) hs
  have hs8 : 8 ≤ s := by
    exact le_trans (le_trans (Nat.le_max_right sCoeff 8) (Nat.le_max_right sN (max sCoeff 8))) hs
  have hspos_nat : 0 < s := by omega
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
  have hk_ge_Cs : C * (s : ℝ) ≤ (k : ℝ) := by
    dsimp [k]
    exact Nat.le_ceil (C * (s : ℝ))
  have hk_ge_s_real : (s : ℝ) ≤ (k : ℝ) := by
    calc
      (s : ℝ) = 1 * (s : ℝ) := by ring_nf
      _ ≤ C * (s : ℝ) := by
        exact mul_le_mul_of_nonneg_right (le_of_lt hC) hspos.le
      _ ≤ (k : ℝ) := hk_ge_Cs
  have hk_pos_nat : 0 < k := by
    have : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le hspos hk_ge_s_real
    exact_mod_cast this
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hp0_nonneg : 0 ≤ p0 := by
    dsimp [p0]
    positivity
  have hNlower : (1 / 2 : ℝ) * A ≤ N := by
    have h := hN s hsN
    norm_num at h ⊢
    simpa [A, N] using h
  have hcoeff_large : 2 ≤ (s : ℝ) / (16 * Real.exp 1) := by
    have hs_ge : 32 * Real.exp 1 ≤ (s : ℝ) := by
      exact le_trans (le_of_lt hsCoeff) (by exact_mod_cast hsCoeff')
    rw [le_div_iff₀ (by positivity : 0 < 16 * Real.exp 1)]
    nlinarith [Real.exp_pos 1]
  have halpha_nonneg : 0 ≤ alpha := by
    have hfrac_lt_one : 1 / (2 * C) < 1 := by
      rw [div_lt_iff₀ h2Cpos]
      nlinarith
    dsimp [alpha]
    exact mul_nonneg (by linarith) hspos.le
  have htarget_ge_one : 1 ≤ target := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
      halpha_nonneg
    simpa [target] using h
  have hA_eq : A = Real.rpow 2 (2 * (s : ℝ) - 3) := by
    dsimp [A]
    have hsub : ((2 * s - 3 : ℕ) : ℝ) = 2 * (s : ℝ) - 3 := by
      norm_num [Nat.cast_sub (by omega : 3 ≤ 2 * s)]
    rw [← hsub]
    norm_num
  have h_exp_compare :
      alpha - 4 ≤ 2 * (s : ℝ) - 4 - E / (k : ℝ) := by
    have hdiv_le : (s : ℝ) ^ 2 / (2 * (k : ℝ)) ≤ (s : ℝ) / (2 * C) := by
      rw [div_le_div_iff₀ (by positivity : 0 < 2 * (k : ℝ)) (by positivity : 0 < 2 * C)]
      nlinarith [hk_ge_Cs, hspos]
    dsimp [alpha, E]
    have hk_ne : (k : ℝ) ≠ 0 := ne_of_gt hk_pos
    field_simp [hk_ne]
    nlinarith [hdiv_le]
  have hpow_exp :
      Real.rpow 2 (alpha - 4) ≤ Real.rpow 2 (2 * (s : ℝ) - 4 - E / (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) h_exp_compare
  have hcoef_s_le_k : (s : ℝ) / Real.exp 1 ≤ (k : ℝ) / Real.exp 1 := by
    exact div_le_div_of_nonneg_right hk_ge_s_real (Real.exp_pos 1).le
  have hpA_lower :
      ((s : ℝ) / Real.exp 1) * Real.rpow 2 (alpha - 4) ≤
        p0 * ((1 / 2 : ℝ) * A) := by
    have hpA_eq :
        p0 * ((1 / 2 : ℝ) * A) =
          ((k : ℝ) / Real.exp 1) * Real.rpow 2 (2 * (s : ℝ) - 4 - E / (k : ℝ)) := by
      dsimp [p0]
      rw [hA_eq]
      have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        norm_num
      change ((k : ℝ) / Real.exp 1 * (2 : ℝ) ^ (-(E / (k : ℝ)))) *
          ((1 / 2 : ℝ) * (2 : ℝ) ^ (2 * (s : ℝ) - 3)) =
        (k : ℝ) / Real.exp 1 * (2 : ℝ) ^ (2 * (s : ℝ) - 4 - E / (k : ℝ))
      rw [hhalf]
      calc
        ((k : ℝ) / Real.exp 1 * (2 : ℝ) ^ (-(E / (k : ℝ)))) *
            ((2 : ℝ) ^ (-1 : ℝ) * (2 : ℝ) ^ (2 * (s : ℝ) - 3))
            = (k : ℝ) / Real.exp 1 *
                ((2 : ℝ) ^ (-(E / (k : ℝ))) *
                  ((2 : ℝ) ^ (-1 : ℝ) * (2 : ℝ) ^ (2 * (s : ℝ) - 3))) := by ring_nf
        _ = (k : ℝ) / Real.exp 1 *
                ((2 : ℝ) ^ (-(E / (k : ℝ))) *
                  (2 : ℝ) ^ ((-1 : ℝ) + (2 * (s : ℝ) - 3))) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ = (k : ℝ) / Real.exp 1 *
                (2 : ℝ) ^ (-(E / (k : ℝ)) + ((-1 : ℝ) + (2 * (s : ℝ) - 3))) := by
              rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        _ = (k : ℝ) / Real.exp 1 *
                (2 : ℝ) ^ (2 * (s : ℝ) - 4 - E / (k : ℝ)) := by
              congr 1
              ring_nf
    calc
      ((s : ℝ) / Real.exp 1) * Real.rpow 2 (alpha - 4)
          ≤ ((k : ℝ) / Real.exp 1) *
              Real.rpow 2 (2 * (s : ℝ) - 4 - E / (k : ℝ)) := by
              exact mul_le_mul hcoef_s_le_k hpow_exp
                (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
                (div_nonneg hk_pos.le (Real.exp_pos 1).le)
      _ = p0 * ((1 / 2 : ℝ) * A) := hpA_eq.symm
  have htarget_coeff :
      2 * target ≤ ((s : ℝ) / Real.exp 1) * Real.rpow 2 (alpha - 4) := by
    have hpow_decomp :
        Real.rpow 2 (alpha - 4) = target / 16 := by
      dsimp [target]
      change (2 : ℝ) ^ (alpha - 4) = (2 : ℝ) ^ alpha / 16
      have hsplit : (2 : ℝ) ^ (alpha - 4) = (2 : ℝ) ^ alpha * (2 : ℝ) ^ (-4 : ℝ) := by
        rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        congr 1
      rw [hsplit]
      norm_num [Real.rpow_natCast]
      ring_nf
    rw [hpow_decomp]
    have htarget_nonneg : 0 ≤ target := by
      dsimp [target]
      positivity
    calc
      2 * target ≤ (s : ℝ) / (16 * Real.exp 1) * target :=
        mul_le_mul_of_nonneg_right hcoeff_large htarget_nonneg
      _ = (s : ℝ) / Real.exp 1 * (target / 16) := by
        field_simp [(Real.exp_pos 1).ne']
  have hpN_lower : 2 * target ≤ p0 * N := by
    calc
      2 * target ≤ ((s : ℝ) / Real.exp 1) * Real.rpow 2 (alpha - 4) := htarget_coeff
      _ ≤ p0 * ((1 / 2 : ℝ) * A) := hpA_lower
      _ ≤ p0 * N := mul_le_mul_of_nonneg_left hNlower hp0_nonneg
  have hfinal : target ≤ p0 * N - 1 := by
    nlinarith [htarget_ge_one, hpN_lower]
  simpa [target, alpha, N] using hfinal
