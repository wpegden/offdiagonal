import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductGeometricSumLeTwoPow]

universe u

theorem StarProductGeometricSumLeTwoPow (K : Type u) [Field K] [Fintype K]
    (q n : ℕ) (hq : q = Fintype.card K) :
    (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ 2 * q ^ n := by
-- BODY
  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Fintype.one_lt_card
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Finset.sum_range_succ]
      calc
        (∑ i ∈ Finset.range (n + 1), q ^ i) + q ^ (n + 1)
            ≤ 2 * q ^ n + q ^ (n + 1) := by
              exact Nat.add_le_add_right ih _
        _ = (2 + q) * q ^ n := by
              rw [pow_succ]
              ring
        _ ≤ (2 * q) * q ^ n := by
              exact Nat.mul_le_mul_right (q ^ n) (by omega : 2 + q ≤ 2 * q)
        _ = 2 * q ^ (n + 1) := by
              rw [pow_succ]
              ring
