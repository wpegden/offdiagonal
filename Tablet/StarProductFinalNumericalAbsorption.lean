import Mathlib.Tactic
import Tablet.Preamble

set_option linter.unusedVariables false

-- [TABLET NODE: StarProductFinalNumericalAbsorption]

theorem StarProductFinalNumericalAbsorption (A C : ℝ) (t q k w : ℕ)
    (ht : 1 ≤ t)
    (hB_nonneg : 0 ≤ A * (q : ℝ) ^ t)
    (hB_ge_one : 1 ≤ A * (q : ℝ) ^ t)
    (hDeltaPow :
      (4 * (q : ℝ) ^ (2 * t - 1)) ^ w ≤ (q : ℝ) ^ (2 * t * w))
    (hqpow : (q : ℝ) ^ (2 * t * w) ≤ (2 : ℝ) ^ k)
    (hC : 4 * A ≤ C) :
    (2 : ℝ) ^ k *
        (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
        (A * (q : ℝ) ^ t) ^ (k - w) ≤
      (C * (q : ℝ) ^ t) ^ k := by
-- BODY
  let B : ℝ := A * (q : ℝ) ^ t
  have hB_nonneg' : 0 ≤ B := by simpa [B] using hB_nonneg
  have hB_ge_one' : 1 ≤ B := by simpa [B] using hB_ge_one
  have htwo_nonneg : 0 ≤ (2 : ℝ) ^ k := by positivity
  have hBpow_nonneg : 0 ≤ B ^ (k - w) := pow_nonneg hB_nonneg' _
  have hBpow_le : B ^ (k - w) ≤ B ^ k :=
    pow_le_pow_right₀ hB_ge_one' (Nat.sub_le k w)
  have hbase_le : 4 * B ≤ C * (q : ℝ) ^ t := by
    have hqpow_nonneg : 0 ≤ (q : ℝ) ^ t := by positivity
    calc
      4 * B = (4 * A) * (q : ℝ) ^ t := by ring
      _ ≤ C * (q : ℝ) ^ t := mul_le_mul_of_nonneg_right hC hqpow_nonneg
  have hfourB_nonneg : 0 ≤ 4 * B := by positivity
  calc
    (2 : ℝ) ^ k *
        (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
        (A * (q : ℝ) ^ t) ^ (k - w)
        = (2 : ℝ) ^ k *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
          B ^ (k - w) := by rfl
    _ = (2 : ℝ) ^ k *
          ((4 * (q : ℝ) ^ (2 * t - 1)) ^ w * B ^ (k - w)) := by ring
    _ ≤ (2 : ℝ) ^ k * (((q : ℝ) ^ (2 * t * w)) * B ^ (k - w)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hDeltaPow hBpow_nonneg) htwo_nonneg
    _ = (2 : ℝ) ^ k * ((q : ℝ) ^ (2 * t * w)) * B ^ (k - w) := by ring
    _ = (2 : ℝ) ^ k * (((q : ℝ) ^ (2 * t * w)) * B ^ (k - w)) := by ring
    _ ≤ (2 : ℝ) ^ k * (((2 : ℝ) ^ k) * B ^ (k - w)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hqpow hBpow_nonneg) htwo_nonneg
    _ = (2 : ℝ) ^ k * ((2 : ℝ) ^ k) * B ^ (k - w) := by ring
    _ ≤ (2 : ℝ) ^ k * ((2 : ℝ) ^ k) * B ^ k := by
      exact mul_le_mul_of_nonneg_left hBpow_le (mul_nonneg htwo_nonneg htwo_nonneg)
    _ = (4 * B) ^ k := by
      rw [← mul_pow, ← mul_pow]
      ring
    _ ≤ (C * (q : ℝ) ^ t) ^ k :=
      pow_le_pow_left₀ hfourB_nonneg hbase_le k
