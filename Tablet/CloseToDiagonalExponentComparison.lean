import Tablet.Preamble

-- [TABLET NODE: CloseToDiagonalExponentComparison]

theorem CloseToDiagonalExponentComparison (s a : ℕ) (delta eta : ℝ)
    (hspos : 0 < (s : ℝ)) (heta : 0 ≤ eta) (hdelta : 0 ≤ delta)
    (ha : (a : ℝ) ≤ delta * (s : ℝ)) :
    (((s : ℝ) + (a : ℝ) - 1) / 2 - (a : ℝ) ^ 2 / (2 * (s : ℝ))) -
        ((5 / 2 : ℝ) * delta + eta) ≤
      2 * (s : ℝ) - 3 -
        (((3 / 2 : ℝ) * (s : ℝ) ^ 2 + (a : ℝ) * (s : ℝ) -
            (5 / 2 : ℝ) * (s : ℝ) + eta * (s : ℝ)) /
          ((s + a : ℕ) : ℝ)) := by
-- BODY
  have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
  have hs_nonneg : 0 ≤ (s : ℝ) := hspos.le
  have hsum_pos : 0 < (s : ℝ) + (a : ℝ) := by positivity
  rw [show ((s + a : ℕ) : ℝ) = (s : ℝ) + (a : ℝ) by norm_num]
  field_simp [hspos.ne', hsum_pos.ne']
  ring_nf
  nlinarith [mul_nonneg ha_nonneg ha_nonneg, mul_nonneg ha_nonneg hdelta,
    mul_nonneg heta hs_nonneg, ha]
