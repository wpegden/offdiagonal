import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductDeltaPowerLeQPower]

theorem StarProductDeltaPowerLeQPower (t q w : ℕ)
    (ht : 1 ≤ t) (hq : 4 ≤ q) :
    (4 * (q : ℝ) ^ (2 * t - 1)) ^ w ≤ (q : ℝ) ^ (2 * t * w) := by
-- BODY
  have hq_nonneg : 0 ≤ (q : ℝ) := by positivity
  have hq_ge_four : (4 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hbase : 4 * (q : ℝ) ^ (2 * t - 1) ≤ (q : ℝ) ^ (2 * t) := by
    have hexp : (2 * t - 1) + 1 = 2 * t := by omega
    calc
      4 * (q : ℝ) ^ (2 * t - 1)
          ≤ (q : ℝ) * (q : ℝ) ^ (2 * t - 1) := by
            exact mul_le_mul_of_nonneg_right hq_ge_four (pow_nonneg hq_nonneg _)
      _ = (q : ℝ) ^ (2 * t - 1) * (q : ℝ) := by ring
      _ = (q : ℝ) ^ ((2 * t - 1) + 1) := by rw [pow_succ]
      _ = (q : ℝ) ^ (2 * t) := by rw [hexp]
  calc
    (4 * (q : ℝ) ^ (2 * t - 1)) ^ w ≤ ((q : ℝ) ^ (2 * t)) ^ w :=
      pow_le_pow_left₀ (by positivity) hbase w
    _ = (q : ℝ) ^ (2 * t * w) := by
      simpa [Nat.mul_assoc] using (pow_mul (q : ℝ) (2 * t) w).symm
