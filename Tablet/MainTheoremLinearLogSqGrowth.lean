import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Tablet.Preamble

-- [TABLET NODE: MainTheoremLinearLogSqGrowth]

open Filter

theorem MainTheoremLinearLogSqGrowth (a B : ℝ) (ha : 0 < a) (hB : 0 < B) :
    ∃ X0 : ℝ, ∀ k : ℕ, X0 ≤ (k : ℝ) →
      B ≤ a * (k : ℝ) / (Real.log (k : ℝ)) ^ 2 := by
-- BODY
  have hcoef : (0 : ℝ) < a / B := by positivity
  have hsmall :
      ∀ᶠ x : ℝ in atTop,
        ‖(Real.log x) ^ 2‖ ≤ (a / B : ℝ) * ‖id x‖ := by
    simpa using (Real.isLittleO_pow_log_id_atTop (n := 2)).def hcoef
  have hlog_large : ∀ᶠ x : ℝ in atTop, (1 : ℝ) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually_ge_atTop 1
  rcases eventually_atTop.1 (hsmall.and hlog_large) with ⟨X0, hX0⟩
  refine ⟨X0, ?_⟩
  intro k hk
  rcases hX0 (k : ℝ) hk with ⟨hsmall_k, hlog_ge_one⟩
  have hk_nonneg : 0 ≤ (k : ℝ) := by positivity
  have hlog_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le zero_lt_one hlog_ge_one
  have hlogsq_pos : 0 < (Real.log (k : ℝ)) ^ 2 := sq_pos_of_ne_zero hlog_pos.ne'
  have hlogsq_nonneg : 0 ≤ (Real.log (k : ℝ)) ^ 2 := le_of_lt hlogsq_pos
  have hbound :
      (Real.log (k : ℝ)) ^ 2 ≤ (a / B : ℝ) * (k : ℝ) := by
    simpa [Real.norm_of_nonneg hlogsq_nonneg,
      Real.norm_of_nonneg hk_nonneg, id] using hsmall_k
  rw [le_div_iff₀ hlogsq_pos]
  calc
    B * (Real.log (k : ℝ)) ^ 2
        ≤ B * ((a / B : ℝ) * (k : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hbound hB.le
    _ = a * (k : ℝ) := by field_simp [hB.ne']

