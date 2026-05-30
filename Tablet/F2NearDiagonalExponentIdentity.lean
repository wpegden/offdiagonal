import Tablet.Preamble

-- [TABLET NODE: F2NearDiagonalExponentIdentity]

theorem F2NearDiagonalExponentIdentity (s k j : ℕ) (hj1 : 1 ≤ j) (hjs : j ≤ s - 1) :
    (((s - 1) * ((s - j) + k) - Nat.choose ((s - j) + 1) 2 : ℕ) : ℝ) =
      (s : ℝ) ^ 2 / 2 + (s : ℝ) * (k : ℝ) -
        (3 / 2 : ℝ) * (s : ℝ) - (k : ℝ) +
          (3 / 2 : ℝ) * (j : ℝ) - (j : ℝ) ^ 2 / 2 := by
-- BODY
  have hs1 : 1 ≤ s := by omega
  have hchoose_le : Nat.choose ((s - j) + 1) 2 ≤ (s - 1) * ((s - j) + k) := by
    rw [Nat.choose_two_right]
    apply Nat.div_le_of_le_mul
    have htle2 : (s - j) + 1 ≤ 2 * (s - 1) := by omega
    have hmul1 : ((s - j) + 1) * (s - j) ≤ (2 * (s - 1)) * (s - j) :=
      Nat.mul_le_mul_right (s - j) htle2
    have htk : s - j ≤ (s - j) + k := Nat.le_add_right (s - j) k
    have hmul2 : (2 * (s - 1)) * (s - j) ≤ (2 * (s - 1)) * ((s - j) + k) :=
      Nat.mul_le_mul_left (2 * (s - 1)) htk
    simpa [Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using hmul1.trans hmul2
  have hchoose_formula :
      (Nat.choose ((s - j) + 1) 2 : ℝ) =
        ((s - j : ℕ) : ℝ) * (((s - j : ℕ) : ℝ) + 1) / 2 := by
    rw [Nat.choose_two_right]
    have hpred : s - j + 1 - 1 = s - j := by omega
    rw [hpred]
    have hdvd : 2 ∣ ((s - j) + 1) * (s - j) := by
      rw [← even_iff_two_dvd]
      simpa [mul_comm] using Nat.even_mul_succ_self (s - j)
    rw [Nat.cast_div hdvd (by norm_num : ((2 : ℕ) : ℝ) ≠ 0)]
    norm_num
    ring
  calc
    (((s - 1) * ((s - j) + k) - Nat.choose ((s - j) + 1) 2 : ℕ) : ℝ)
        = (((s - 1) * ((s - j) + k) : ℕ) : ℝ) -
            (Nat.choose ((s - j) + 1) 2 : ℝ) := by
          exact Nat.cast_sub hchoose_le
    _ = ((s - 1 : ℕ) : ℝ) * (((s - j : ℕ) : ℝ) + (k : ℝ)) -
            (((s - j : ℕ) : ℝ) * (((s - j : ℕ) : ℝ) + 1) / 2) := by
          rw [hchoose_formula]
          norm_num
    _ = (s : ℝ) ^ 2 / 2 + (s : ℝ) * (k : ℝ) -
        (3 / 2 : ℝ) * (s : ℝ) - (k : ℝ) +
          (3 / 2 : ℝ) * (j : ℝ) - (j : ℝ) ^ 2 / 2 := by
          have hsj_cast : ((s - j : ℕ) : ℝ) = (s : ℝ) - (j : ℝ) := by
            exact Nat.cast_sub (by omega : j ≤ s)
          have hs1_cast : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
            rw [Nat.cast_sub hs1]
            norm_num
          rw [hsj_cast, hs1_cast]
          ring
