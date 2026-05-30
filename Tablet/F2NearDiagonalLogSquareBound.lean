import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- [TABLET NODE: F2NearDiagonalLogSquareBound]

open Filter in
open scoped Topology in
theorem F2NearDiagonalLogSquareBound (eps : ℝ) (heps : 0 < eps) :
    ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      (Real.logb 2 (2 * Real.exp 1 * (s : ℝ)) + (3 / 2 : ℝ)) ^ 2 / 2 ≤
        eps * (s : ℝ) / 4 := by
-- BODY
  let C : ℝ := 2 * Real.exp 1
  have hCpos : 0 < C := by dsimp [C]; positivity
  have hCne : C ≠ 0 := ne_of_gt hCpos
  have hinvC_ne : C⁻¹ ≠ 0 := inv_ne_zero hCne
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC_atTop : Tendsto (fun x : ℝ => C * x) atTop atTop :=
    tendsto_id.const_mul_atTop hCpos
  have hsq_base :
      Tendsto (fun y : ℝ => Real.log y ^ 2 / (C⁻¹ * y + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop C⁻¹ 0 2 hinvC_ne
  have hsq :
      Tendsto (fun x : ℝ => Real.log (C * x) ^ 2 / x) atTop (𝓝 0) := by
    have hcomp := hsq_base.comp hC_atTop
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hCx_ne : C * x ≠ 0 := mul_ne_zero hCne hx.ne'
    simp only [Function.comp_apply, add_zero]
    field_simp [hCx_ne, hCne, hx.ne']
  have hlin_base :
      Tendsto (fun y : ℝ => Real.log y ^ 1 / (C⁻¹ * y + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop C⁻¹ 0 1 hinvC_ne
  have hlin :
      Tendsto (fun x : ℝ => Real.log (C * x) / x) atTop (𝓝 0) := by
    have hcomp := hlin_base.comp hC_atTop
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hCx_ne : C * x ≠ 0 := mul_ne_zero hCne hx.ne'
    simp only [Function.comp_apply, add_zero]
    field_simp [hCx_ne, hCne, hx.ne']
  have hinv_base :
      Tendsto (fun y : ℝ => Real.log y ^ 0 / (C⁻¹ * y + 0)) atTop (𝓝 0) :=
    Real.tendsto_pow_log_div_mul_add_atTop C⁻¹ 0 0 hinvC_ne
  have hinv :
      Tendsto (fun x : ℝ => (1 : ℝ) / x) atTop (𝓝 0) := by
    have hcomp := hinv_base.comp hC_atTop
    refine hcomp.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hCx_ne : C * x ≠ 0 := mul_ne_zero hCne hx.ne'
    simp only [Function.comp_apply, add_zero]
    field_simp [hCx_ne, hCne, hx.ne']
  have htend_real :
      Tendsto
        (fun x : ℝ =>
          ((Real.logb 2 (C * x) + (3 / 2 : ℝ)) ^ 2 / 2) / x)
        atTop (𝓝 0) := by
    have hcomb :
        Tendsto
          (fun x : ℝ =>
            (1 / (2 * (Real.log 2) ^ 2)) * (Real.log (C * x) ^ 2 / x) +
              (3 / (2 * Real.log 2)) * (Real.log (C * x) / x) +
                (9 / 8 : ℝ) * ((1 : ℝ) / x))
          atTop (𝓝 0) := by
      simpa using ((hsq.const_mul _).add (hlin.const_mul _)).add (hinv.const_mul _)
    refine hcomb.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    have hlog2_ne : Real.log 2 ≠ 0 := ne_of_gt hlog2_pos
    rw [Real.logb]
    field_simp [hlog2_ne, hx.ne']
    ring
  have htend_nat :
      Tendsto
        (fun s : ℕ =>
          ((Real.logb 2 (C * (s : ℝ)) + (3 / 2 : ℝ)) ^ 2 / 2) / (s : ℝ))
        atTop (𝓝 0) :=
    htend_real.comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ s : ℕ in atTop,
      ((Real.logb 2 (C * (s : ℝ)) + (3 / 2 : ℝ)) ^ 2 / 2) / (s : ℝ) < eps / 4 :=
    htend_nat.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < eps / 4))
  rcases eventually_atTop.mp hev with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro s hs
  have hsN : N ≤ s := by omega
  have hspos_nat : 0 < s := by omega
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
  have hlt := hN s hsN
  have hmain : (Real.logb 2 (C * (s : ℝ)) + (3 / 2 : ℝ)) ^ 2 / 2 <
      eps * (s : ℝ) / 4 := by
    rw [div_lt_iff₀ hspos] at hlt
    linarith
  dsimp [C] at hmain ⊢
  exact hmain.le
