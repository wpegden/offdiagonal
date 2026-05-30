import Tablet.F2BadTupleFixedIncreaseFalseExponentBound

-- [TABLET NODE: F2BadTupleFixedIncreaseTrueExponentBound]

theorem F2BadTupleFixedIncreaseTrueExponentBound (p m u : ℕ) (hu : u + 1 ≤ p) :
    2 ^ (p * (u + m) - Nat.choose (u + 1) 2) *
        (2 ^ p * 2 ^ (p - (u + 1))) ≤
      2 ^ (p * ((u + 1) + (m + 1)) - Nat.choose ((u + 1) + 1) 2) := by
-- BODY
  rw [← pow_add, ← pow_add]
  apply Nat.pow_le_pow_right
  · norm_num
  · have hu' : u ≤ p := by
      omega
    have hc_le : Nat.choose (u + 1) 2 ≤ p * (u + m) := by
      rw [Nat.choose_two_right]
      apply Nat.div_le_of_le_mul
      have h1 : (u + 1) * (u + 1 - 1) = (u + 1) * u := by
        simp
      rw [h1]
      nlinarith [Nat.mul_le_mul_right u hu',
        Nat.mul_le_mul_left p (Nat.le_add_right u m)]
    have hmul : p * ((u + 1) + (m + 1)) = p * (u + m) + 2 * p := by
      ring
    have hchoose :
        Nat.choose ((u + 1) + 1) 2 = Nat.choose (u + 1) 2 + (u + 1) := by
      rw [show (u + 1) + 1 = Nat.succ (u + 1) by rfl]
      rw [show 2 = Nat.succ 1 by rfl]
      rw [Nat.choose_succ_succ]
      rw [Nat.choose_one_right]
      omega
    omega
