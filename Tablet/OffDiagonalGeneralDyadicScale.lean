import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.FieldTheory.Finite.GaloisField
import Tablet.Preamble

-- [TABLET NODE: OffDiagonalGeneralDyadicScale]

noncomputable section

open Filter
open scoped Classical

theorem OffDiagonalGeneralDyadicScale (delta : ℝ) (hdelta_pos : 0 < delta)
    (_hdelta_lt : delta < 1 / 10) :
    ∃ X0 : ℝ, ∀ x : ℝ, X0 ≤ x →
      ∃ m : ℕ, 1 ≤ m ∧
        let q : ℕ := 2 ^ m
        Nat.card (GaloisField 2 m) = q ∧
          (q : ℝ) ≤ (delta / 100) * x / Real.log x ∧
          (delta / 100) * x / Real.log x ≤ 2 * (q : ℝ) ∧
          Real.rpow x (1 - delta / 2) ≤ (q : ℝ) ∧
          1 ≤ x ∧ 1 ≤ Real.log x ∧
          Real.log (q : ℝ) ≤ Real.log x ∧
          0 < Real.log (q : ℝ) := by
-- BODY
  have hdelta_half_pos : 0 < delta / 2 := by positivity
  have hsmall_id :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x‖ ≤ (delta / 200 : ℝ) * ‖id x‖ := by
    simpa using (Real.isLittleO_log_id_atTop).def
      (by positivity : (0 : ℝ) < delta / 200)
  have hsmall_rpow :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log x‖ ≤ (delta / 200 : ℝ) * ‖x ^ (delta / 2)‖ := by
    simpa using (isLittleO_log_rpow_atTop hdelta_half_pos).def
      (by positivity : (0 : ℝ) < delta / 200)
  have hlog_large : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hx_large : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop 1
  have hboth :
      ∀ᶠ x : ℝ in atTop,
        ∃ m : ℕ, 1 ≤ m ∧
          let q : ℕ := 2 ^ m
          Nat.card (GaloisField 2 m) = q ∧
            (q : ℝ) ≤ (delta / 100) * x / Real.log x ∧
            (delta / 100) * x / Real.log x ≤ 2 * (q : ℝ) ∧
            Real.rpow x (1 - delta / 2) ≤ (q : ℝ) ∧
            1 ≤ x ∧ 1 ≤ Real.log x ∧
            Real.log (q : ℝ) ≤ Real.log x ∧
            0 < Real.log (q : ℝ) := by
    filter_upwards [hsmall_id, hsmall_rpow, hlog_large, hx_large] with
      x hlog_id hlog_rpow hlog_ge_one hx_ge_one
    have hlog_pos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog_ge_one
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_ge_one
    have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
    have hlog_nonneg : 0 ≤ Real.log x := le_of_lt hlog_pos
    have hlog_le_id : Real.log x ≤ (delta / 200) * x := by
      simpa [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hx_nonneg, id] using
        hlog_id
    have hrpow_nonneg : 0 ≤ x ^ (delta / 2) := le_of_lt (Real.rpow_pos_of_pos hx_pos _)
    have hlog_le_rpow : Real.log x ≤ (delta / 200) * x ^ (delta / 2) := by
      simpa [Real.norm_of_nonneg hlog_nonneg, Real.norm_of_nonneg hrpow_nonneg] using
        hlog_rpow
    let y : ℝ := (delta / 100) * x / Real.log x
    have hy_ge_two : (2 : ℝ) ≤ y := by
      dsimp [y]
      rw [le_div_iff₀ hlog_pos]
      nlinarith
    have hy_ge_one : (1 : ℝ) ≤ y := le_trans (by norm_num) hy_ge_two
    rcases exists_nat_pow_near hy_ge_one (by norm_num : (1 : ℝ) < 2) with
      ⟨m, hmle, hmlt⟩
    have hm_pos : 1 ≤ m := by
      by_contra hnot
      have hm0 : m = 0 := by omega
      have hy_lt_two : y < 2 := by
        simpa [hm0] using hmlt
      linarith
    have hm_ne : m ≠ 0 := by omega
    refine ⟨m, hm_pos, ?_, ?_, ?_, ?_, hx_ge_one, hlog_ge_one, ?_, ?_⟩
    · simpa using GaloisField.card 2 m hm_ne
    · have hmle_nat : ((2 ^ m : ℕ) : ℝ) ≤ y := by
        simpa using hmle
      simpa [y]
    · have hy_lt_two_pow : y < (2 : ℝ) * ((2 ^ m : ℕ) : ℝ) := by
        have hcast : ((2 : ℝ) ^ (m + 1)) = (2 : ℝ) * ((2 : ℝ) ^ m) := by
          rw [pow_succ]
          ring
        have hpow_cast : ((2 : ℝ) ^ m) = ((2 ^ m : ℕ) : ℝ) := by norm_num
        calc
          y < (2 : ℝ) ^ (m + 1) := hmlt
          _ = (2 : ℝ) * ((2 ^ m : ℕ) : ℝ) := by rw [hcast, hpow_cast]
      exact le_of_lt hy_lt_two_pow
    · have hmul_rpow : x ^ (1 - delta / 2) * x ^ (delta / 2) = x := by
        calc
          x ^ (1 - delta / 2) * x ^ (delta / 2)
              = x ^ ((1 - delta / 2) + delta / 2) := by
                rw [Real.rpow_add hx_pos]
          _ = x := by
                ring_nf
                rw [Real.rpow_one]
      have hpow_le_y_half : x ^ (1 - delta / 2) ≤ y / 2 := by
        dsimp [y]
        rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
        rw [le_div_iff₀ hlog_pos]
        calc
          x ^ (1 - delta / 2) * 2 * Real.log x
              ≤ x ^ (1 - delta / 2) * 2 * ((delta / 200) * x ^ (delta / 2)) := by
                gcongr
          _ = delta / 100 * x := by
                calc
                  x ^ (1 - delta / 2) * 2 * (delta / 200 * x ^ (delta / 2))
                      = (delta / 100) *
                          (x ^ (1 - delta / 2) * x ^ (delta / 2)) := by
                        ring
                  _ = delta / 100 * x := by rw [hmul_rpow]
      have hy_half_le_q : y / 2 ≤ ((2 ^ m : ℕ) : ℝ) := by
        have hy_lt_two_pow : y < (2 : ℝ) * ((2 ^ m : ℕ) : ℝ) := by
          have hcast : ((2 : ℝ) ^ (m + 1)) = (2 : ℝ) * ((2 : ℝ) ^ m) := by
            rw [pow_succ]
            ring
          have hpow_cast : ((2 : ℝ) ^ m) = ((2 ^ m : ℕ) : ℝ) := by norm_num
          calc
            y < (2 : ℝ) ^ (m + 1) := hmlt
            _ = (2 : ℝ) * ((2 ^ m : ℕ) : ℝ) := by rw [hcast, hpow_cast]
        nlinarith
      exact hpow_le_y_half.trans hy_half_le_q
    · have hmle_nat : ((2 ^ m : ℕ) : ℝ) ≤ y := by
        simpa using hmle
      have hcoef_le_one : delta / 100 ≤ (1 : ℝ) := by nlinarith
      have hcoef_nonneg : 0 ≤ delta / 100 := by positivity
      have hx_div_log_le_x : x / Real.log x ≤ x := by
        rw [div_le_iff₀ hlog_pos]
        nlinarith
      have hy_le_x : y ≤ x := by
        dsimp [y]
        calc
          delta / 100 * x / Real.log x = (delta / 100) * (x / Real.log x) := by ring
          _ ≤ 1 * x := by
            exact mul_le_mul hcoef_le_one hx_div_log_le_x (by positivity) (by positivity)
          _ = x := by ring
      exact Real.log_le_log (by positivity) (hmle_nat.trans hy_le_x)
    · have htwo_le_q : (2 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
        exact_mod_cast Nat.pow_le_pow_right (by omega : (1 : ℕ) ≤ 2) hm_pos
      have hq_gt_one : (1 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by linarith
      exact Real.log_pos hq_gt_one
  simpa [Filter.eventually_atTop] using hboth
