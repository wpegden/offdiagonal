import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductHLeDelta]

theorem StarProductHLeDelta (A : ℝ) (t q h Delta : ℕ)
    (ht : 2 ≤ t)
    (hq : 1 ≤ q)
    (hh : (h : ℝ) ≤ A * (q : ℝ) ^ t)
    (hA : A ≤ 4 * (q : ℝ) ^ (t - 1))
    (hDelta : 4 * q ^ (2 * t - 1) ≤ Delta) :
    h ≤ Delta := by
-- BODY
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hpow_nonneg : 0 ≤ (q : ℝ) ^ t := pow_nonneg hq_nonneg _
  have hmain_real :
      (h : ℝ) ≤ (4 * q ^ (2 * t - 1) : ℕ) := by
    calc
      (h : ℝ) ≤ A * (q : ℝ) ^ t := hh
      _ ≤ (4 * (q : ℝ) ^ (t - 1)) * (q : ℝ) ^ t := by
        exact mul_le_mul_of_nonneg_right hA hpow_nonneg
      _ = 4 * (q : ℝ) ^ (2 * t - 1) := by
        have hexp : (t - 1) + t = 2 * t - 1 := by omega
        calc
          (4 * (q : ℝ) ^ (t - 1)) * (q : ℝ) ^ t
              = 4 * ((q : ℝ) ^ (t - 1) * (q : ℝ) ^ t) := by ring
          _ = 4 * (q : ℝ) ^ ((t - 1) + t) := by rw [← pow_add]
          _ = 4 * (q : ℝ) ^ (2 * t - 1) := by rw [hexp]
      _ = (4 * q ^ (2 * t - 1) : ℕ) := by norm_num
  have h_to_base : h ≤ 4 * q ^ (2 * t - 1) := by
    exact_mod_cast hmain_real
  exact h_to_base.trans hDelta
