import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.FieldTheory.Finite.GaloisField
import Tablet.Preamble

-- [TABLET NODE: MainTheoremDyadicFieldScale]

noncomputable section

open Filter
open scoped Classical

theorem MainTheoremDyadicFieldScale (C : ℝ) (hC : 0 < C) :
    ∃ c : ℝ, 0 < c ∧ ∃ X0 : ℝ, ∀ k : ℕ, X0 ≤ (k : ℝ) →
      ∃ m : ℕ, 1 ≤ m ∧
        let q : ℕ := 2 ^ m
        Nat.card (GaloisField 2 m) = q ∧
          C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ) ∧
          (k : ℝ) ≤ 4 * C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ∧
          C ≤ (q : ℝ) ∧
          4 ≤ q ∧
          Real.log (q : ℝ) ≤ Real.log (k : ℝ) ∧
          c * (k : ℝ) / (Real.log (k : ℝ)) ^ 2 ≤ (q : ℝ) := by
-- BODY
  let c : ℝ := 1 / (2 * C)
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc_pos, ?_⟩
  have hcoef_loglog_pos : (0 : ℝ) < 1 / 16 := by norm_num
  have hsmall_loglog :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log (Real.log x)‖ ≤ (1 / 16 : ℝ) * ‖Real.log x‖ := by
    simpa [Function.comp_def] using
      (Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop).def
        hcoef_loglog_pos
  have hsmall_const :
      ∀ᶠ x : ℝ in atTop,
        ‖Real.log (2 * C)‖ ≤ (1 / 16 : ℝ) * ‖Real.log x‖ := by
    simpa using
      (Real.isLittleO_const_log_atTop (c := Real.log (2 * C))).def hcoef_loglog_pos
  have hcoef_C_pos : (0 : ℝ) < 1 / (2 * C * C) := by positivity
  have hsmall_logsq_C :
      ∀ᶠ x : ℝ in atTop,
        ‖(Real.log x) ^ 2‖ ≤ (1 / (2 * C * C) : ℝ) * ‖id x‖ := by
    simpa using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).def hcoef_C_pos
  have hcoef_four_pos : (0 : ℝ) < 1 / (8 * C) := by positivity
  have hsmall_logsq_four :
      ∀ᶠ x : ℝ in atTop,
        ‖(Real.log x) ^ 2‖ ≤ (1 / (8 * C) : ℝ) * ‖id x‖ := by
    simpa using
      (Real.isLittleO_pow_log_id_atTop (n := 2)).def hcoef_four_pos
  have hlog_large : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  have hlog_large_C : ∀ᶠ x : ℝ in atTop, (1 / C : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop (1 / C)
  have hx_large : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ x := eventually_ge_atTop 1
  have hreal_event :
      ∀ᶠ x : ℝ in atTop,
        ∃ m : ℕ, 1 ≤ m ∧
          let q : ℕ := 2 ^ m
          Nat.card (GaloisField 2 m) = q ∧
            C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ x ∧
            x ≤ 4 * C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ∧
            C ≤ (q : ℝ) ∧
            4 ≤ q ∧
            Real.log (q : ℝ) ≤ Real.log x ∧
            c * x / (Real.log x) ^ 2 ≤ (q : ℝ) := by
    filter_upwards [hsmall_loglog, hsmall_const, hsmall_logsq_C,
      hsmall_logsq_four, hlog_large, hlog_large_C, hx_large] with
      x hloglog_abs hconst_abs hlogsq_C_abs hlogsq_four_abs
      hlog_ge_one hlog_ge_invC hx_ge_one
    have hx_pos : 0 < x := lt_of_lt_of_le zero_lt_one hx_ge_one
    have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
    have hlog_pos : 0 < Real.log x := lt_of_lt_of_le zero_lt_one hlog_ge_one
    have hlog_nonneg : 0 ≤ Real.log x := le_of_lt hlog_pos
    have hlog_ne : Real.log x ≠ 0 := hlog_pos.ne'
    have hlogsq_pos : 0 < (Real.log x) ^ 2 := sq_pos_of_ne_zero hlog_ne
    have hlogsq_nonneg : 0 ≤ (Real.log x) ^ 2 := le_of_lt hlogsq_pos
    have hloglog_bound :
        Real.log (Real.log x) ≤ (1 / 16 : ℝ) * Real.log x := by
      calc
        Real.log (Real.log x) ≤ ‖Real.log (Real.log x)‖ := le_abs_self _
        _ ≤ (1 / 16 : ℝ) * ‖Real.log x‖ := hloglog_abs
        _ = (1 / 16 : ℝ) * Real.log x := by
          rw [Real.norm_of_nonneg hlog_nonneg]
    have hconst_bound :
        Real.log (2 * C) ≤ (1 / 16 : ℝ) * Real.log x := by
      calc
        Real.log (2 * C) ≤ ‖Real.log (2 * C)‖ := le_abs_self _
        _ ≤ (1 / 16 : ℝ) * ‖Real.log x‖ := hconst_abs
        _ = (1 / 16 : ℝ) * Real.log x := by
          rw [Real.norm_of_nonneg hlog_nonneg]
    have hden_log_bound :
        Real.log (2 * C) + 2 * Real.log (Real.log x) ≤
          (1 / 4 : ℝ) * Real.log x := by
      nlinarith
    have hlogsq_le_C :
        (Real.log x) ^ 2 ≤ (1 / (2 * C * C) : ℝ) * x := by
      simpa [Real.norm_of_nonneg hlogsq_nonneg, Real.norm_of_nonneg hx_nonneg, id]
        using hlogsq_C_abs
    have hlogsq_le_four :
        (Real.log x) ^ 2 ≤ (1 / (8 * C) : ℝ) * x := by
      simpa [Real.norm_of_nonneg hlogsq_nonneg, Real.norm_of_nonneg hx_nonneg, id]
        using hlogsq_four_abs
    let y : ℝ := x / (2 * C * (Real.log x) ^ 2)
    have hden_pos : 0 < 2 * C * (Real.log x) ^ 2 := by positivity
    have hden_ne : 2 * C * (Real.log x) ^ 2 ≠ 0 := hden_pos.ne'
    have htwoC_pos : 0 < 2 * C := by positivity
    have htwoC_ne : 2 * C ≠ 0 := htwoC_pos.ne'
    have hlogsq_ne : (Real.log x) ^ 2 ≠ 0 := hlogsq_pos.ne'
    have hy_pos : 0 < y := by
      dsimp [y]
      positivity
    have htwoCC_logs_le_x : 2 * C * C * (Real.log x) ^ 2 ≤ x := by
      calc
        2 * C * C * (Real.log x) ^ 2
            ≤ 2 * C * C * ((1 / (2 * C * C) : ℝ) * x) := by
              gcongr
        _ = x := by
              field_simp [hC.ne']
    have heightC_logs_le_x : 8 * C * (Real.log x) ^ 2 ≤ x := by
      calc
        8 * C * (Real.log x) ^ 2
            ≤ 8 * C * ((1 / (8 * C) : ℝ) * x) := by
              gcongr
        _ = x := by
              field_simp [hC.ne']
    have hy_ge_C : C ≤ y := by
      dsimp [y]
      rw [le_div_iff₀ hden_pos]
      nlinarith
    have hy_ge_four_real : (4 : ℝ) ≤ y := by
      dsimp [y]
      rw [le_div_iff₀ hden_pos]
      nlinarith
    have hy_ge_one : (1 : ℝ) ≤ y := by nlinarith
    rcases exists_nat_pow_near hy_ge_one (by norm_num : (1 : ℝ) < 2) with
      ⟨n, hnle, hnlt⟩
    let m : ℕ := n + 1
    let q : ℕ := 2 ^ m
    have hm_pos : 1 ≤ m := by
      dsimp [m]
      omega
    have hm_ne : m ≠ 0 := by omega
    have hnle_nat : ((2 ^ n : ℕ) : ℝ) ≤ y := by
      have hpow_cast : ((2 : ℝ) ^ n) = ((2 ^ n : ℕ) : ℝ) := by norm_num
      simpa only [← hpow_cast] using hnle
    have hy_le_q : y ≤ (q : ℝ) := by
      have hpow_cast : ((2 : ℝ) ^ (n + 1)) = ((2 ^ (n + 1) : ℕ) : ℝ) := by
        norm_num
      have : y < (q : ℝ) := by
        dsimp [q, m]
        simpa only [← hpow_cast] using hnlt
      exact le_of_lt this
    have hq_le_two_y : (q : ℝ) ≤ 2 * y := by
      have hpow_succ_cast :
          ((2 ^ (n + 1) : ℕ) : ℝ) = (2 : ℝ) * ((2 ^ n : ℕ) : ℝ) := by
        calc
          ((2 ^ (n + 1) : ℕ) : ℝ) = ((2 ^ n * 2 : ℕ) : ℝ) := by rw [pow_succ]
          _ = ((2 ^ n : ℕ) : ℝ) * (2 : ℝ) := by norm_num
          _ = (2 : ℝ) * ((2 ^ n : ℕ) : ℝ) := by ring
      dsimp [q, m]
      calc
        ((2 ^ (n + 1) : ℕ) : ℝ)
            = (2 : ℝ) * ((2 ^ n : ℕ) : ℝ) := hpow_succ_cast
        _ ≤ 2 * y := by gcongr
    have hq_ge_C : C ≤ (q : ℝ) := hy_ge_C.trans hy_le_q
    have hq_ge_four_real : (4 : ℝ) ≤ (q : ℝ) := hy_ge_four_real.trans hy_le_q
    have hq_ge_four_nat : 4 ≤ q := by
      exact_mod_cast hq_ge_four_real
    have hq_pos : 0 < (q : ℝ) := by nlinarith
    have hlogq_pos : 0 < Real.log (q : ℝ) := by
      exact Real.log_pos (by nlinarith)
    have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := le_of_lt hlogq_pos
    have hq_le_scaled : (q : ℝ) ≤ x / (C * (Real.log x) ^ 2) := by
      have htwo_y :
          2 * y = x / (C * (Real.log x) ^ 2) := by
        dsimp [y]
        field_simp [hC.ne', hlog_ne]
      simpa [htwo_y] using hq_le_two_y
    have hone_le_C_log : (1 : ℝ) ≤ C * Real.log x := by
      have h := (div_le_iff₀ hC).mp hlog_ge_invC
      simpa [mul_comm] using h
    have hone_le_C_logsq : (1 : ℝ) ≤ C * (Real.log x) ^ 2 := by
      have hprod : (1 : ℝ) * 1 ≤ (C * Real.log x) * Real.log x :=
        mul_le_mul hone_le_C_log hlog_ge_one (by norm_num)
          (le_trans (by norm_num) hone_le_C_log)
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ (C * Real.log x) * Real.log x := hprod
        _ = C * (Real.log x) ^ 2 := by ring
    have hx_div_le_x : x / (C * (Real.log x) ^ 2) ≤ x := by
      have hdenC_pos : 0 < C * (Real.log x) ^ 2 := by positivity
      rw [div_le_iff₀ hdenC_pos]
      calc
        x ≤ x * 1 := by rw [mul_one]
        _ ≤ x * (C * (Real.log x) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hone_le_C_logsq hx_nonneg
    have hq_le_x : (q : ℝ) ≤ x := by
      exact le_trans hq_le_scaled hx_div_le_x
    have hlogq_le_logx : Real.log (q : ℝ) ≤ Real.log x :=
      Real.log_le_log hq_pos hq_le_x
    have hlog_y_eq :
        Real.log y =
          Real.log x - (Real.log (2 * C) + 2 * Real.log (Real.log x)) := by
      dsimp [y]
      rw [Real.log_div hx_pos.ne' hden_ne]
      rw [Real.log_mul htwoC_ne hlogsq_ne]
      rw [Real.log_pow]
      ring
    have hlog_y_lower : (3 / 4 : ℝ) * Real.log x ≤ Real.log y := by
      rw [hlog_y_eq]
      linarith
    have hlogx_le_four_thirds_logy : Real.log x ≤ (4 / 3 : ℝ) * Real.log y := by
      linarith
    have hlog_y_le_logq : Real.log y ≤ Real.log (q : ℝ) :=
      Real.log_le_log hy_pos hy_le_q
    have hlogx_le_four_thirds_logq :
        Real.log x ≤ (4 / 3 : ℝ) * Real.log (q : ℝ) := by
      linarith
    have hlogx_sq_le_two_logq_sq :
        (Real.log x) ^ 2 ≤ 2 * (Real.log (q : ℝ)) ^ 2 := by
      have hfactor_nonneg : 0 ≤ (4 / 3 : ℝ) * Real.log (q : ℝ) := by positivity
      have hsquare :
          (Real.log x) ^ 2 ≤ ((4 / 3 : ℝ) * Real.log (q : ℝ)) ^ 2 := by
        exact (sq_le_sq₀ hlog_nonneg hfactor_nonneg).2 hlogx_le_four_thirds_logq
      have hfactor :
          ((4 / 3 : ℝ) * Real.log (q : ℝ)) ^ 2 ≤
            2 * (Real.log (q : ℝ)) ^ 2 := by
        calc
          ((4 / 3 : ℝ) * Real.log (q : ℝ)) ^ 2
              = (16 / 9 : ℝ) * (Real.log (q : ℝ)) ^ 2 := by ring
          _ ≤ 2 * (Real.log (q : ℝ)) ^ 2 := by
              linarith [sq_nonneg (Real.log (q : ℝ))]
      exact hsquare.trans hfactor
    have hlogq_sq_le_logx_sq :
        (Real.log (q : ℝ)) ^ 2 ≤ (Real.log x) ^ 2 := by
      exact (sq_le_sq₀ hlogq_nonneg hlog_nonneg).2 hlogq_le_logx
    have hscale_lower :
        C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ x := by
      have hCq_nonneg : 0 ≤ C * (q : ℝ) := by positivity
      have hpart1 :
          C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤
            C * (q : ℝ) * (Real.log x) ^ 2 :=
        mul_le_mul_of_nonneg_left hlogq_sq_le_logx_sq hCq_nonneg
      have hpart2 :
          C * (q : ℝ) * (Real.log x) ^ 2 ≤
            C * (x / (C * (Real.log x) ^ 2)) * (Real.log x) ^ 2 := by
        have hleft : C * (q : ℝ) ≤ C * (x / (C * (Real.log x) ^ 2)) :=
          mul_le_mul_of_nonneg_left hq_le_scaled (le_of_lt hC)
        exact mul_le_mul_of_nonneg_right hleft hlogsq_nonneg
      calc
        C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2
            ≤ C * (q : ℝ) * (Real.log x) ^ 2 := hpart1
        _ ≤ C * (x / (C * (Real.log x) ^ 2)) * (Real.log x) ^ 2 := hpart2
        _ = x := by
              field_simp [hC.ne', hlog_ne]
    have hscale_upper :
        x ≤ 4 * C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by
      have hx_le_twoC :
          x ≤ 2 * C * (q : ℝ) * (Real.log x) ^ 2 := by
        have h := (div_le_iff₀ hden_pos).mp hy_le_q
        calc
          x ≤ (q : ℝ) * (2 * C * (Real.log x) ^ 2) := h
          _ = 2 * C * (q : ℝ) * (Real.log x) ^ 2 := by ring
      have hcoef_nonneg : 0 ≤ 2 * C * (q : ℝ) := by positivity
      calc
        x ≤ 2 * C * (q : ℝ) * (Real.log x) ^ 2 := hx_le_twoC
        _ ≤ 2 * C * (q : ℝ) * (2 * (Real.log (q : ℝ)) ^ 2) :=
              mul_le_mul_of_nonneg_left hlogx_sq_le_two_logq_sq hcoef_nonneg
        _ = 4 * C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 := by ring
    have hcomparison :
        c * x / (Real.log x) ^ 2 ≤ (q : ℝ) := by
      dsimp [c]
      have hrewrite :
          (1 / (2 * C) : ℝ) * x / (Real.log x) ^ 2 =
            x / (2 * C * (Real.log x) ^ 2) := by
        field_simp [hC.ne', hlog_ne]
      rw [hrewrite]
      exact hy_le_q
    refine ⟨m, hm_pos, ?_, hscale_lower, hscale_upper, hq_ge_C,
      hq_ge_four_nat, hlogq_le_logx, hcomparison⟩
    simpa [q] using GaloisField.card 2 m hm_ne
  rcases (Filter.eventually_atTop.1 hreal_event) with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro k hk
  exact hX0 (k : ℝ) hk
