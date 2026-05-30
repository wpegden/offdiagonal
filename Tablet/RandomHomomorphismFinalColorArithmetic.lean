import Tablet.Preamble

-- [TABLET NODE: RandomHomomorphismFinalColorArithmetic]

theorem RandomHomomorphismFinalColorArithmetic (ell s n : ℕ) (_hell : 3 ≤ ell)
    (hn : (n : ℝ) ≤
      Real.rpow 2 (((s : ℝ) / 2 - 4) * ((ell - 1 : ℕ) : ℝ))) :
    (n : ℝ) ^ s *
        Real.rpow 2 (((-(s : ℝ) ^ 2 / 2 + 4 * (s : ℝ)) *
          ((ell - 1 : ℕ) : ℝ))) ≤
      1 := by
-- BODY
  let A : ℝ := (((s : ℝ) / 2 - 4) * ((ell - 1 : ℕ) : ℝ))
  let B : ℝ := ((-(s : ℝ) ^ 2 / 2 + 4 * (s : ℝ)) *
    ((ell - 1 : ℕ) : ℝ))
  have hn_pow :
      (n : ℝ) ^ s ≤ (Real.rpow 2 A) ^ s := by
    exact pow_le_pow_left₀ (by positivity : 0 ≤ (n : ℝ)) (by simpa [A] using hn) s
  have hB_nonneg : 0 ≤ Real.rpow 2 B :=
    Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _
  calc
    (n : ℝ) ^ s * Real.rpow 2 (((-(s : ℝ) ^ 2 / 2 + 4 * (s : ℝ)) *
          ((ell - 1 : ℕ) : ℝ)))
        = (n : ℝ) ^ s * Real.rpow 2 B := by simp [B]
    _ ≤ (Real.rpow 2 A) ^ s * Real.rpow 2 B := by
      exact mul_le_mul_of_nonneg_right hn_pow hB_nonneg
    _ = 1 := by
      have hpow :
          (Real.rpow 2 A) ^ s = Real.rpow 2 (A * (s : ℝ)) := by
        calc
          (Real.rpow 2 A) ^ s = Real.rpow (Real.rpow 2 A) (s : ℝ) := by
            exact (Real.rpow_natCast (Real.rpow 2 A) s).symm
          _ = Real.rpow 2 (A * (s : ℝ)) := by
            exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2) A (s : ℝ)).symm
      have hmul :
          Real.rpow 2 (A * (s : ℝ)) * Real.rpow 2 B =
            Real.rpow 2 (A * (s : ℝ) + B) := by
        change (2 : ℝ) ^ (A * (s : ℝ)) * (2 : ℝ) ^ B =
          (2 : ℝ) ^ (A * (s : ℝ) + B)
        rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      rw [hpow, hmul]
      have hexp : A * (s : ℝ) + B = 0 := by
        dsimp [A, B]
        ring
      rw [hexp]
      norm_num
