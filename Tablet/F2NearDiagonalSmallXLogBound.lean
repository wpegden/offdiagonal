import Tablet.Preamble
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

-- [TABLET NODE: F2NearDiagonalSmallXLogBound]

open Filter in
open scoped Topology in
theorem F2NearDiagonalSmallXLogBound (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ x : ℝ, 0 < x → x ≤ delta →
        x * Real.logb 2 (2 * Real.exp 1 / x) ≤ eps / 4 := by
-- BODY
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hconst :
      Tendsto (fun x : ℝ => x * Real.log (2 * Real.exp 1)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hx : Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
      tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
    simpa [mul_comm, zero_mul] using hx.const_mul (Real.log (2 * Real.exp 1))
  have hxlog :
      Tendsto (fun x : ℝ => x * Real.log x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := tendsto_log_mul_rpow_nhdsGT_zero (show (0 : ℝ) < 1 by norm_num)
    simpa [Real.rpow_one, mul_comm] using h
  have hnatlog :
      Tendsto (fun x : ℝ => x * Real.log (2 * Real.exp 1 / x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hsub := hconst.sub hxlog
    have heq :
        (fun x : ℝ => x * Real.log (2 * Real.exp 1) - x * Real.log x) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun x : ℝ => x * Real.log (2 * Real.exp 1 / x)) := by
      filter_upwards [self_mem_nhdsWithin] with x hx
      have hxpos : 0 < x := hx
      have hnum_ne : 2 * Real.exp 1 ≠ 0 := by positivity
      have hx_ne : x ≠ 0 := ne_of_gt hxpos
      rw [Real.log_div hnum_ne hx_ne]
      ring
    simpa using hsub.congr' heq
  have htend :
      Tendsto (fun x : ℝ => x * Real.logb 2 (2 * Real.exp 1 / x)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hscale := hnatlog.const_mul (Real.log 2)⁻¹
    have heq :
        (fun x : ℝ => (Real.log 2)⁻¹ * (x * Real.log (2 * Real.exp 1 / x))) =ᶠ[𝓝[>] (0 : ℝ)]
          (fun x : ℝ => x * Real.logb 2 (2 * Real.exp 1 / x)) := by
      filter_upwards with x
      rw [Real.logb, mul_div_assoc, inv_mul_eq_div]
      ring
    simpa [mul_comm, mul_left_comm, mul_assoc] using hscale.congr' heq
  have hev : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ),
      x * Real.logb 2 (2 * Real.exp 1 / x) < eps / 4 :=
    htend.eventually (Iio_mem_nhds (by linarith : (0 : ℝ) < eps / 4))
  have hev_nhds :
      ∀ᶠ x : ℝ in 𝓝 (0 : ℝ),
        x ∈ Set.Ioi (0 : ℝ) → x * Real.logb 2 (2 * Real.exp 1 / x) < eps / 4 :=
    eventually_nhdsWithin_iff.mp hev
  rcases Metric.eventually_nhds_iff.mp hev_nhds with ⟨η, hηpos, hη⟩
  refine ⟨min (η / 2) 1, ?_, ?_, ?_⟩
  · exact lt_min (half_pos hηpos) zero_lt_one
  · exact min_le_right _ _
  · intro x hxpos hxle
    have hxlt_eta : dist x (0 : ℝ) < η := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hxpos]
      have hxle_eta2 : x ≤ η / 2 := hxle.trans (min_le_left _ _)
      linarith
    exact (hη hxlt_eta hxpos).le
