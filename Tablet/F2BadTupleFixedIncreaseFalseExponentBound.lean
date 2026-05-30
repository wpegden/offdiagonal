import Tablet.Preamble

-- [TABLET NODE: F2BadTupleFixedIncreaseFalseExponentBound]

theorem F2BadTupleFixedIncreaseFalseExponentBound (p m u : ℕ) (hu : u ≤ p) :
    2 ^ (p * (u + m) - Nat.choose (u + 1) 2) *
        (2 ^ u * 2 ^ (p - u)) ≤
      2 ^ (p * (u + (m + 1)) - Nat.choose (u + 1) 2) := by
-- BODY
  have hfac : 2 ^ u * 2 ^ (p - u) = 2 ^ p := by
    rw [← pow_add]
    congr 1
    omega
  rw [hfac]
  rw [← pow_add]
  apply Nat.pow_le_pow_right
  · norm_num
  · have hc_le : Nat.choose (u + 1) 2 ≤ p * (u + m) := by
      rw [Nat.choose_two_right]
      apply Nat.div_le_of_le_mul
      have h1 : (u + 1) * (u + 1 - 1) = (u + 1) * u := by
        simp
      rw [h1]
      nlinarith [Nat.mul_le_mul_right u hu,
        Nat.mul_le_mul_left p (Nat.le_add_right u m)]
    have hmul : p * (u + (m + 1)) = p * (u + m) + p := by
      ring
    omega
