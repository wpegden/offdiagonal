import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductShrinkThresholdCollapse]

theorem StarProductShrinkThresholdCollapse (q t e : ℕ) (N rho : ℝ)
    (hN : N ≤ 2 * (q : ℝ) ^ t)
    (hrhoPow_nonneg : 0 ≤ rho ^ e)
    (hqpow_pos : 0 < (q : ℝ) ^ t)
    (hfactor : rho ^ e < 1 / (4 * (q : ℝ) ^ t)) :
    N * rho ^ e < 1 := by
-- BODY
  have htwoQ_pos : 0 < 2 * (q : ℝ) ^ t := by positivity
  have hle : N * rho ^ e ≤ (2 * (q : ℝ) ^ t) * rho ^ e :=
    mul_le_mul_of_nonneg_right hN hrhoPow_nonneg
  have hlt :
      (2 * (q : ℝ) ^ t) * rho ^ e <
        (2 * (q : ℝ) ^ t) * (1 / (4 * (q : ℝ) ^ t)) :=
    mul_lt_mul_of_pos_left hfactor htwoQ_pos
  calc
    N * rho ^ e ≤ (2 * (q : ℝ) ^ t) * rho ^ e := hle
    _ < (2 * (q : ℝ) ^ t) * (1 / (4 * (q : ℝ) ^ t)) := hlt
    _ = 1 / 2 := by
      field_simp [ne_of_gt hqpow_pos]
      ring
    _ < 1 := by norm_num
