import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.FieldTheory.Finite.GaloisField
import Tablet.Preamble

-- [TABLET NODE: MainTheoremDyadicGaloisScale]

noncomputable section

open Filter
open scoped Classical

theorem MainTheoremDyadicGaloisScale (s : ℕ) (_hs : 4 ≤ s) :
    ∃ k0 : ℕ, ∃ A B M : ℝ,
      0 < A ∧ 0 < B ∧ 0 < M ∧
      (1 : ℝ) ≤ A ∧ (1 : ℝ) ≤ B ∧
      (100 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ 3) ≤ A ∧
      (((s + 1 : ℕ) : ℝ) ≤ M) ∧
      B ^ (s + 1) * (((s + 1 : ℕ) : ℝ) ^ 2) ≤ M ∧
      (200 : ℝ) * B ^ (s + 1) ≤ M ∧
      ∀ k : ℕ, k0 ≤ k →
      ∃ m : ℕ, 1 ≤ m ∧
        let q : ℕ := 2 ^ m
        Nat.card (GaloisField 2 m) = q ∧
          (k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2) ≤ (q : ℝ) ∧
          (q : ℝ) ≤ (k : ℝ) / (A * (Real.log (k : ℝ)) ^ 2) ∧
          Real.log (q : ℝ) ≤ Real.log (k : ℝ) ∧
          0 < Real.log (q : ℝ) ∧
          (1 : ℝ) ≤ Real.log (k : ℝ) ∧
          M * (Real.log (k : ℝ)) ^ (2 * s + 2) ≤ (k : ℝ) := by
-- BODY
  let A : ℝ := (1000000 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ 4)
  let B : ℝ := 2 * A
  let M : ℝ := (1000000 : ℝ) * (B ^ (s + 1)) * (((s + 1 : ℕ) : ℝ) ^ (2 * s + 2))
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hM_pos : 0 < M := by
    dsimp [M]
    positivity
  have hA_ge_one : (1 : ℝ) ≤ A := by
    dsimp [A]
    have hs1 : (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
    have hpow : (1 : ℝ) ≤ (((s + 1 : ℕ) : ℝ) ^ 4) := by
      simpa using (one_le_pow₀ hs1 : (1 : ℝ) ≤ (((s + 1 : ℕ) : ℝ) ^ 4))
    nlinarith
  have hB_ge_one : (1 : ℝ) ≤ B := by
    dsimp [B]
    nlinarith
  let S : ℝ := ((s + 1 : ℕ) : ℝ)
  have hS_ge_one : (1 : ℝ) ≤ S := by
    dsimp [S]
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
  have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one hS_ge_one
  have hA_large : (100 : ℝ) * S ^ 3 ≤ A := by
    dsimp [A, S]
    have hS_nonneg : (0 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) := by positivity
    calc
      (100 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ 3)
          ≤ (1000000 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ 3 * ((s + 1 : ℕ) : ℝ)) := by
            nlinarith [hS_ge_one]
      _ = (1000000 : ℝ) * (((s + 1 : ℕ) : ℝ) ^ 4) := by ring
  have hS_le_M : S ≤ M := by
    dsimp [M, S]
    have hBpow_ge_one : (1 : ℝ) ≤ B ^ (s + 1) := one_le_pow₀ hB_ge_one
    have hSpow_ge_S : ((s + 1 : ℕ) : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ (2 * s + 2) := by
      have hpow_right :
          ((s + 1 : ℕ) : ℝ) ^ 1 ≤ ((s + 1 : ℕ) : ℝ) ^ (2 * s + 2) :=
        pow_le_pow_right₀ hS_ge_one (by omega : 1 ≤ 2 * s + 2)
      simpa using hpow_right
    have hS_le_prod :
        ((s + 1 : ℕ) : ℝ) ≤ B ^ (s + 1) * ((s + 1 : ℕ) : ℝ) ^ (2 * s + 2) := by
      calc
        ((s + 1 : ℕ) : ℝ)
            ≤ 1 * ((s + 1 : ℕ) : ℝ) ^ (2 * s + 2) := by
              simpa using hSpow_ge_S
        _ ≤ B ^ (s + 1) * ((s + 1 : ℕ) : ℝ) ^ (2 * s + 2) := by
              exact mul_le_mul_of_nonneg_right hBpow_ge_one (by positivity)
    nlinarith
  have hBpowS_le_M : B ^ (s + 1) * S ^ 2 ≤ M := by
    dsimp [M, S]
    have hBpow_nonneg : (0 : ℝ) ≤ B ^ (s + 1) := by positivity
    have hSpow_ge_two :
        ((s + 1 : ℕ) : ℝ) ^ 2 ≤ ((s + 1 : ℕ) : ℝ) ^ (2 * s + 2) :=
      pow_le_pow_right₀ hS_ge_one (by omega : 2 ≤ 2 * s + 2)
    have hmul :=
      mul_le_mul_of_nonneg_left hSpow_ge_two hBpow_nonneg
    nlinarith
  have hBpow200_le_M : (200 : ℝ) * B ^ (s + 1) ≤ M := by
    dsimp [M, S]
    have hBpow_nonneg : (0 : ℝ) ≤ B ^ (s + 1) := by positivity
    have hSpow_ge_one :
        (1 : ℝ) ≤ ((s + 1 : ℕ) : ℝ) ^ (2 * s + 2) :=
      one_le_pow₀ hS_ge_one
    have hmul :=
      mul_le_mul_of_nonneg_left hSpow_ge_one hBpow_nonneg
    nlinarith
  have hlarge :
      ∃ k0 : ℕ, ∀ k : ℕ, k0 ≤ k →
        (2 : ℝ) ≤ (k : ℝ) / (A * (Real.log (k : ℝ)) ^ 2) ∧
        (1 : ℝ) ≤ Real.log (k : ℝ) ∧
        M * (Real.log (k : ℝ)) ^ (2 * s + 2) ≤ (k : ℝ) := by
    have hsmallR :
        ∀ᶠ x : ℝ in atTop,
          ‖Real.log x ^ 2‖ ≤ (1 / (2 * A) : ℝ) * ‖id x‖ := by
      simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).def
        (by positivity : (0 : ℝ) < 1 / (2 * A))
    have hsmallNat :
        ∀ᶠ k : ℕ in atTop,
          ‖Real.log (k : ℝ) ^ 2‖ ≤ (1 / (2 * A) : ℝ) * ‖(k : ℝ)‖ :=
      tendsto_natCast_atTop_atTop.eventually hsmallR
    have hlogNat : ∀ᶠ k : ℕ in atTop, (1 : ℝ) ≤ Real.log (k : ℝ) :=
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    have hgrowthR :
        ∀ᶠ x : ℝ in atTop,
          ‖Real.log x ^ (2 * s + 2)‖ ≤ (1 / M : ℝ) * ‖id x‖ := by
      simpa using (Real.isLittleO_pow_log_id_atTop (n := 2 * s + 2)).def
        (by positivity : (0 : ℝ) < 1 / M)
    have hgrowthNat :
        ∀ᶠ k : ℕ in atTop,
          ‖Real.log (k : ℝ) ^ (2 * s + 2)‖ ≤ (1 / M : ℝ) * ‖(k : ℝ)‖ :=
      tendsto_natCast_atTop_atTop.eventually hgrowthR
    have hboth :
        ∀ᶠ k : ℕ in atTop,
          (2 : ℝ) ≤ (k : ℝ) / (A * (Real.log (k : ℝ)) ^ 2) ∧
          (1 : ℝ) ≤ Real.log (k : ℝ) ∧
          M * (Real.log (k : ℝ)) ^ (2 * s + 2) ≤ (k : ℝ) := by
      filter_upwards [hsmallNat, hlogNat, hgrowthNat] with k hsmall hlog hgrowth
      have hlog_sq_nonneg : (0 : ℝ) ≤ Real.log (k : ℝ) ^ 2 := sq_nonneg _
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
      have hlog_sq_le :
          Real.log (k : ℝ) ^ 2 ≤ (1 / (2 * A) : ℝ) * (k : ℝ) := by
        simpa [Real.norm_of_nonneg hlog_sq_nonneg, Real.norm_of_nonneg hk_nonneg] using
          hsmall
      have hden_pos : (0 : ℝ) < Real.log (k : ℝ) ^ 2 := by positivity
      have hAden_pos : (0 : ℝ) < A * Real.log (k : ℝ) ^ 2 := by positivity
      have hAlog_le : A * Real.log (k : ℝ) ^ 2 ≤ (1 / 2 : ℝ) * (k : ℝ) := by
        calc
          A * Real.log (k : ℝ) ^ 2
              ≤ A * ((1 / (2 * A) : ℝ) * (k : ℝ)) :=
                mul_le_mul_of_nonneg_left hlog_sq_le (le_of_lt hA_pos)
          _ = (1 / 2 : ℝ) * (k : ℝ) := by
                field_simp [ne_of_gt hA_pos]
      have hlog_growth_nonneg : (0 : ℝ) ≤ Real.log (k : ℝ) ^ (2 * s + 2) := by
        positivity
      have hgrowth_le :
          Real.log (k : ℝ) ^ (2 * s + 2) ≤ (1 / M : ℝ) * (k : ℝ) := by
        simpa [Real.norm_of_nonneg hlog_growth_nonneg, Real.norm_of_nonneg hk_nonneg] using
          hgrowth
      have hMlog_le :
          M * Real.log (k : ℝ) ^ (2 * s + 2) ≤ (k : ℝ) := by
        calc
          M * Real.log (k : ℝ) ^ (2 * s + 2)
              ≤ M * ((1 / M : ℝ) * (k : ℝ)) :=
                mul_le_mul_of_nonneg_left hgrowth_le (le_of_lt hM_pos)
          _ = (k : ℝ) := by
                field_simp [ne_of_gt hM_pos]
      constructor
      · rw [le_div_iff₀ hAden_pos]
        nlinarith
      · exact ⟨hlog, hMlog_le⟩
    simpa [Filter.eventually_atTop] using hboth
  rcases hlarge with ⟨k0, hk0⟩
  refine ⟨k0, A, B, M, hA_pos, hB_pos, hM_pos, hA_ge_one, hB_ge_one,
    hA_large, hS_le_M, hBpowS_le_M, hBpow200_le_M, ?_⟩
  intro k hk
  rcases hk0 k hk with ⟨hscale, hlogone, hgrowth⟩
  let x : ℝ := (k : ℝ) / (A * (Real.log (k : ℝ)) ^ 2)
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hscale
  rcases exists_nat_pow_near hx1 (by norm_num : (1 : ℝ) < 2) with ⟨m, hmle, hmlt⟩
  have hm_pos : 1 ≤ m := by
    by_contra hnot
    have hm0 : m = 0 := by omega
    have hxlt2 : x < 2 := by
      simpa [hm0] using hmlt
    linarith
  have hm_ne : m ≠ 0 := by omega
  refine ⟨m, hm_pos, ?_, ?_, ?_, ?_, ?_, hlogone, hgrowth⟩
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
    simpa [x, B, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv_le
  · have hmle_nat : ((2 ^ m : ℕ) : ℝ) ≤ x := by
      simpa using hmle
    simpa [x] using hmle_nat
  · have hden_ge_one : (1 : ℝ) ≤ (Real.log (k : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (k : ℝ) - 1)]
    have hden_pos : (0 : ℝ) < (Real.log (k : ℝ)) ^ 2 := lt_of_lt_of_le zero_lt_one hden_ge_one
    have hx_le_k : x ≤ (k : ℝ) := by
      dsimp [x]
      have hAden_pos : (0 : ℝ) < A * (Real.log (k : ℝ)) ^ 2 := by positivity
      have hAden_ge_one : (1 : ℝ) ≤ A * (Real.log (k : ℝ)) ^ 2 := by
        nlinarith [mul_le_mul hA_ge_one hden_ge_one (by norm_num : (0 : ℝ) ≤ 1)
          (le_of_lt hA_pos)]
      rw [div_le_iff₀ hAden_pos]
      have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
      nlinarith [hk_nonneg, hAden_ge_one]
    have hmle_nat : ((2 ^ m : ℕ) : ℝ) ≤ x := by
      simpa using hmle
    exact Real.log_le_log (by positivity) (le_trans hmle_nat hx_le_k)
  · have htwo_le_q : (2 : ℝ) ≤ ((2 ^ m : ℕ) : ℝ) := by
      exact_mod_cast Nat.pow_le_pow_right (by omega : (1 : ℕ) ≤ 2) hm_pos
    have hq_gt_one : (1 : ℝ) < ((2 ^ m : ℕ) : ℝ) := by linarith
    exact Real.log_pos hq_gt_one
