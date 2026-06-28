import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductPoorExpanderMixingBound]

theorem StarProductPoorExpanderMixingBound (q t : ℕ) (X Y eZell eZr L : ℝ)
    (hq : 0 < (q : ℝ))
    (hXnonneg : 0 ≤ X) (hYleX : Y ≤ X)
    (hpoorUpper : eZell ≤ X / (8 * (q : ℝ)))
    (hmixLower : X / (4 * (q : ℝ)) - L * Real.sqrt X ≤ eZell)
    (hLnonneg : 0 ≤ L)
    (hLsq : 64 * (q : ℝ) ^ 2 * L ^ 2 ≤ 1024 * (q : ℝ) ^ (t + 1))
    (hmixUpper : eZr ≤ (4 / (q : ℝ)) * Y + L * Real.sqrt Y)
    (hLsqrt : L * Real.sqrt (1024 * (q : ℝ) ^ (t + 1)) ≤
      904 * (q : ℝ) ^ t) :
    eZr ≤ 5000 * (q : ℝ) ^ t := by
-- BODY
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq
  have hXbound : X ≤ 1024 * (q : ℝ) ^ (t + 1) := by
    by_cases hXzero : X = 0
    · subst X
      positivity
    · have hXpos : 0 < X := lt_of_le_of_ne' hXnonneg hXzero
      have hsqrt_pos : 0 < Real.sqrt X := Real.sqrt_pos.2 hXpos
      have hsqrt_sq : (Real.sqrt X) ^ 2 = X := by
        rw [Real.sq_sqrt hXnonneg]
      have hmain_raw : X / (4 * (q : ℝ)) - L * Real.sqrt X ≤
          X / (8 * (q : ℝ)) := hmixLower.trans hpoorUpper
      have hmain_scaled : X ≤ 8 * (q : ℝ) * (L * Real.sqrt X) := by
        field_simp [hqne] at hmain_raw ⊢
        nlinarith [hmain_raw]
      have hmain_scaled' : (Real.sqrt X) ^ 2 ≤
          8 * (q : ℝ) * (L * Real.sqrt X) := by
        simpa [hsqrt_sq] using hmain_scaled
      have hsqrt_le : Real.sqrt X ≤ 8 * (q : ℝ) * L := by
        nlinarith [hmain_scaled', hsqrt_pos]
      have hsq_le : X ≤ (8 * (q : ℝ) * L) ^ 2 := by
        rw [← hsqrt_sq]
        nlinarith [hsqrt_le, Real.sqrt_nonneg X, hq, hLnonneg]
      have hconst : (8 * (q : ℝ) * L) ^ 2 = 64 * (q : ℝ) ^ 2 * L ^ 2 := by
        ring
      exact hsq_le.trans (by simpa [hconst] using hLsq)
  have hYbound : Y ≤ 1024 * (q : ℝ) ^ (t + 1) := hYleX.trans hXbound
  have hsqrtY :
      L * Real.sqrt Y ≤ L * Real.sqrt (1024 * (q : ℝ) ^ (t + 1)) := by
    exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hYbound) hLnonneg
  have hfirst :
      (4 / (q : ℝ)) * Y ≤ 4096 * (q : ℝ) ^ t := by
    have hcoef_nonneg : 0 ≤ 4 / (q : ℝ) := by positivity
    have htmp : (4 / (q : ℝ)) * Y ≤
        (4 / (q : ℝ)) * (1024 * (q : ℝ) ^ (t + 1)) := by
      exact mul_le_mul_of_nonneg_left hYbound hcoef_nonneg
    have heq : (4 / (q : ℝ)) * (1024 * (q : ℝ) ^ (t + 1)) =
        4096 * (q : ℝ) ^ t := by
      rw [pow_succ]
      field_simp [hqne]
      ring
    simpa [heq] using htmp
  calc
    eZr ≤ (4 / (q : ℝ)) * Y + L * Real.sqrt Y := hmixUpper
    _ ≤ 4096 * (q : ℝ) ^ t + 904 * (q : ℝ) ^ t := by
      exact add_le_add hfirst (hsqrtY.trans hLsqrt)
    _ ≤ 5000 * (q : ℝ) ^ t := by
      ring_nf
      exact le_rfl
