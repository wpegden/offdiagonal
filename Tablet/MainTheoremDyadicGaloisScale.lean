import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Tablet.Preamble

-- [TABLET NODE: MainTheoremDyadicGaloisScale]

noncomputable section

open Filter
open scoped Classical

theorem MainTheoremDyadicGaloisScale (s : ℕ) (_hs : 4 ≤ s) :
    ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
      ∃ m : ℕ, 1 ≤ m ∧
        let q : ℕ := 2 ^ m
        Nat.card (GaloisField 2 m) = q ∧
          (k : ℝ) / (2 * (Real.log (k : ℝ)) ^ 2) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ (k : ℝ) / (Real.log (k : ℝ)) ^ 2 ∧
          Real.log (q : ℝ) ≤ Real.log (k : ℝ) ∧
          0 < Real.log (q : ℝ) := by
-- BODY
  have hlarge :
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        (2 : ℝ) ≤ (k : ℝ) / (Real.log (k : ℝ)) ^ 2 ∧
        (1 : ℝ) ≤ Real.log (k : ℝ) := by
    have hsmallR :
        ∀ᶠ x : ℝ in atTop,
          ‖Real.log x ^ 2‖ ≤ (1 / 2 : ℝ) * ‖id x‖ := by
      simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).def
        (by norm_num : (0 : ℝ) < 1 / 2)
    have hsmallNat :
        ∀ᶠ k : ℕ in atTop,
          ‖Real.log (k : ℝ) ^ 2‖ ≤ (1 / 2 : ℝ) * ‖(k : ℝ)‖ :=
      tendsto_natCast_atTop_atTop.eventually hsmallR
    have hlogNat : ∀ᶠ k : ℕ in atTop, (1 : ℝ) ≤ Real.log (k : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    have hboth :
        ∀ᶠ k : ℕ in atTop,
          (2 : ℝ) ≤ (k : ℝ) / (Real.log (k : ℝ)) ^ 2 ∧
          (1 : ℝ) ≤ Real.log (k : ℝ) := by
      filter_upwards [hsmallNat, hlogNat] with k hsmall hlog
      have hlog_sq_nonneg : (0 : ℝ) ≤ Real.log (k : ℝ) ^ 2 := sq_nonneg _
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hlog_sq_le :
          Real.log (k : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * (k : ℝ) := by
        simpa [Real.norm_of_nonneg hlog_sq_nonneg, Real.norm_of_nonneg hk_nonneg] using
          hsmall
      have hden_pos : (0 : ℝ) < Real.log (k : ℝ) ^ 2 := by positivity
      constructor
      · rw [le_div_iff₀ hden_pos]
        nlinarith
      · exact hlog
    simpa [Filter.eventually_atTop] using hboth
  rcases hlarge with ⟨k0, hk0⟩
  refine ⟨k0, ?_⟩
  intro k hk
  rcases hk0 k hk with ⟨hscale, hlogone⟩
  let x : ℝ := (k : ℝ) / (Real.log (k : ℝ)) ^ 2
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hscale
  rcases exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2) with ⟨m, hmle, hmlt⟩
  have hm_pos : 1 ≤ m := by
    by_contra hnot
    have hm0 : m = 0 := by omega
    have hxlt2 : x < 2 := by
      simpa [hm0] using hmlt
    linarith
  have hm_ne : m ≠ 0 := by omega
  refine ⟨m, hm_pos, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using GaloisField.card 2 m hm_ne
  · have hx_lt_two_pow : x < (2 : ℝ) * ((2 ^ m : ℕ) : ℝ) := by
      have hcast : ((2 : ℝ) ^ (m + 1)) = (2 : ℝ) * ((2 : ℝ) ^ m) := by
        rw [pow_succ]
        ring
      have hpow_cast : ((2 : ℝ) ^ m) = ((2 ^ m : ℕ) : ℝ) := by norm_num
      calc
        x < (2 : ℝ) ^ (m + 1) := hmlt
        _ = (2 : ℝ) * ((2 ^ m : ℕ) : ℝ) := by rw [hcast, hpow_cast]
    have hdiv_le : x / 2 ≤ ((2 ^ m : ℕ) : ℝ) := by linarith
    simpa [x, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv_le
  · have hmle_nat : ((2 ^ m : ℕ) : ℝ) ≤ x := by
      simpa using hmle
    simpa [x] using hmle_nat
  · have hden_ge_one : (1 : ℝ) ≤ (Real.log (k : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (k : ℝ) - 1)]
    have hden_pos : (0 : ℝ) < (Real.log (k : ℝ)) ^ 2 := lt_of_lt_of_le zero_lt_one hden_ge_one
    have hx_le_k : x ≤ (k : ℝ) := by
      dsimp [x]
      rw [div_le_iff₀ hden_pos]
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith [hk_nonneg, hden_ge_one]
    have hmle_nat : ((2 ^ m : ℕ) : ℝ) ≤ x := by
      simpa using hmle
    exact Real.log_le_log (by positivity) (le_trans hmle_nat hx_le_k)
  · have htwo_le_q : (2 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : (1 : ℕ) ≤ 2) hm_pos
    have hq_gt_one : (1 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by linarith
    exact Real.log_pos hq_gt_one
