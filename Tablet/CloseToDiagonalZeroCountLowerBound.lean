import Tablet.CloseToDiagonalVertexCountLowerBound

-- [TABLET NODE: CloseToDiagonalZeroCountLowerBound]

open Filter in
theorem CloseToDiagonalZeroCountLowerBound (eps delta : ℝ) (heps : 0 < eps)
    (_hdelta_nonneg : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 2) :
    ∃ s0 : ℕ, 4 ≤ s0 ∧ ∀ s a : ℕ, s0 ≤ s →
      (a : ℝ) ≤ delta * (s : ℝ) →
      (1 - eps) * ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
        ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) := by
-- BODY
  by_cases heps_one : 1 ≤ eps
  · refine ⟨4, le_rfl, ?_⟩
    intro s a hs ha
    have hcoef_nonpos : 1 - eps ≤ 0 := by linarith
    have hscale_nonneg :
        0 ≤ ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) := by
      exact mul_nonneg (div_nonneg (by positivity) (Real.exp_pos 1).le)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    have hlhs_nonpos :
        (1 - eps) * (((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ)))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos hscale_nonneg
    have hrhs_nonneg :
        0 ≤ ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) := by
      positivity
    nlinarith [hlhs_nonpos, hrhs_nonneg]
  · have heps_lt_one : eps < 1 := lt_of_not_ge heps_one
    have hrho_pos : 0 < eps / 2 := by positivity
    rcases CloseToDiagonalVertexCountLowerBound (eps / 2) hrho_pos with
      ⟨sN, hsN4, hN⟩
    refine ⟨max sN 8, by omega, ?_⟩
    intro s a hs ha
    have hsN : sN ≤ s := le_trans (Nat.le_max_left sN 8) hs
    have hs8 : 8 ≤ s := le_trans (Nat.le_max_right sN 8) hs
    have hvertex := hN s hsN
    have hspos_nat : 0 < s := by omega
    have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
    have hs_nonneg : 0 ≤ (s : ℝ) := hspos.le
    have hsone : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 1 ≤ s)
    have ha_half : (a : ℝ) ≤ (1 / 2 : ℝ) * (s : ℝ) := by
      exact le_trans ha (mul_le_mul_of_nonneg_right hdelta_le hs_nonneg)
    have hexponent_le :
        ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
          3 * (s : ℝ) / 4 := by
      have hsden_nonneg : 0 ≤ 2 * (s : ℝ) := by positivity
      have hsqterm_nonneg :
          0 ≤ ((a : ℝ) ^ 2) / (2 * (s : ℝ)) :=
        div_nonneg (sq_nonneg _) hsden_nonneg
      nlinarith
    have hrpow_exp_le :
        Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
          Real.rpow 2 (3 * (s : ℝ) / 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent_le
    have hs_le_two_pow_nat : s ≤ 2 ^ (s - 1) := by
      have h : ∀ n : ℕ, n + 1 ≤ 2 ^ n := by
        intro n
        induction n with
        | zero => norm_num
        | succ n ih =>
            rw [pow_succ]
            nlinarith [ih, pow_nonneg (by norm_num : (0 : ℕ) ≤ 2) n]
      have hs_eq : s = (s - 1) + 1 := by omega
      rw [hs_eq]
      exact h (s - 1)
    have h_exp_ge_one : (1 : ℝ) ≤ Real.exp 1 := by
      rw [Real.one_le_exp_iff]
      norm_num
    have hdiv_le_s : (s : ℝ) / Real.exp 1 ≤ (s : ℝ) := by
      rw [div_le_iff₀ (Real.exp_pos 1)]
      nlinarith
    have hs_le_pow_real : (s : ℝ) ≤ ((2 ^ (s - 1) : ℕ) : ℝ) := by
      exact_mod_cast hs_le_two_pow_nat
    have hpow_nat_eq :
        ((2 ^ (s - 1) : ℕ) : ℝ) = Real.rpow 2 ((s : ℝ) - 1) := by
      have hsub : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
        norm_num [Nat.cast_sub (by omega : 1 ≤ s)]
      rw [← hsub]
      norm_num
    have hcoef_le : (s : ℝ) / Real.exp 1 ≤ Real.rpow 2 ((s : ℝ) - 1) := by
      calc
        (s : ℝ) / Real.exp 1 ≤ (s : ℝ) := hdiv_le_s
        _ ≤ ((2 ^ (s - 1) : ℕ) : ℝ) := hs_le_pow_real
        _ = Real.rpow 2 ((s : ℝ) - 1) := hpow_nat_eq
    have hscale_le :
        ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
        Real.rpow 2 ((s : ℝ) - 1) * Real.rpow 2 (3 * (s : ℝ) / 4) :=
      mul_le_mul hcoef_le hrpow_exp_le
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
        (le_trans (div_nonneg (by positivity) (Real.exp_pos 1).le) hcoef_le)
    have hprod_eq :
        Real.rpow 2 ((s : ℝ) - 1) * Real.rpow 2 (3 * (s : ℝ) / 4) =
          Real.rpow 2 (7 * (s : ℝ) / 4 - 1) := by
      change (2 : ℝ) ^ ((s : ℝ) - 1) * (2 : ℝ) ^ (3 * (s : ℝ) / 4) =
          (2 : ℝ) ^ (7 * (s : ℝ) / 4 - 1)
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring
    have hexp_big_le : 7 * (s : ℝ) / 4 - 1 ≤ 2 * (s : ℝ) - 3 := by
      nlinarith [show (8 : ℝ) ≤ (s : ℝ) by exact_mod_cast hs8]
    have hpow_big_le :
        Real.rpow 2 (7 * (s : ℝ) / 4 - 1) ≤ Real.rpow 2 (2 * (s : ℝ) - 3) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_big_le
    have hpow_big_eq :
        Real.rpow 2 (2 * (s : ℝ) - 3) = ((2 ^ (2 * s - 3) : ℕ) : ℝ) := by
      have hsub : ((2 * s - 3 : ℕ) : ℝ) = 2 * (s : ℝ) - 3 := by
        norm_num [Nat.cast_sub (by omega : 3 ≤ 2 * s)]
      rw [← hsub]
      norm_num
    have hB_le_A :
        ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
        ((2 ^ (2 * s - 3) : ℕ) : ℝ) := by
      calc
        ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ)))
            ≤ Real.rpow 2 ((s : ℝ) - 1) * Real.rpow 2 (3 * (s : ℝ) / 4) :=
              hscale_le
        _ = Real.rpow 2 (7 * (s : ℝ) / 4 - 1) := hprod_eq
        _ ≤ Real.rpow 2 (2 * (s : ℝ) - 3) := hpow_big_le
        _ = ((2 ^ (2 * s - 3) : ℕ) : ℝ) := hpow_big_eq
    have hcoef_nonneg : 0 ≤ 1 - eps := by linarith
    have hA_nonneg : 0 ≤ ((2 ^ (2 * s - 3) : ℕ) : ℝ) := by positivity
    calc
      (1 - eps) * ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ)))
          ≤ (1 - eps) * ((2 ^ (2 * s - 3) : ℕ) : ℝ) := by
            simpa [mul_assoc] using mul_le_mul_of_nonneg_left hB_le_A hcoef_nonneg
      _ ≤ (1 - eps / 2) * ((2 ^ (2 * s - 3) : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_right (by linarith) hA_nonneg
      _ ≤ ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) :=
            hvertex
