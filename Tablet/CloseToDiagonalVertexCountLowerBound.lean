import Tablet.Preamble

-- [TABLET NODE: CloseToDiagonalVertexCountLowerBound]

open Filter in
theorem CloseToDiagonalVertexCountLowerBound (rho : ℝ) (hrho : 0 < rho) :
    ∃ s0 : ℕ, 4 ≤ s0 ∧ ∀ s : ℕ, s0 ≤ s →
      (1 - rho) * (((2 ^ (2 * s - 3) : ℕ) : ℝ)) ≤
        ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) := by
-- BODY
  have hpow_tendsto :
      Tendsto (fun n : ℕ => (2 : ℝ) ^ n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)
  rcases eventually_atTop.1 ((tendsto_atTop.1 hpow_tendsto) (3 / rho)) with
    ⟨N, hN⟩
  refine ⟨max (N + 1) 4, Nat.le_max_right (N + 1) 4, ?_⟩
  intro s hs
  have hs4 : 4 ≤ s := le_trans (Nat.le_max_right (N + 1) 4) hs
  have hNle : N ≤ s - 1 := by
    have hN1 : N + 1 ≤ s := le_trans (Nat.le_max_left (N + 1) 4) hs
    omega
  have hpow_ge : 3 / rho ≤ (2 : ℝ) ^ (s - 1) := hN (s - 1) hNle
  have hlarge : (3 : ℝ) ≤ rho * ((2 : ℝ) ^ (s - 1)) := by
    calc
      (3 : ℝ) = rho * (3 / rho) := by field_simp [hrho.ne']
      _ ≤ rho * ((2 : ℝ) ^ (s - 1)) :=
        mul_le_mul_of_nonneg_left hpow_ge hrho.le
  have hsmall_le_big_nat : 2 ^ (s - 1) + 2 ^ (s - 2) ≤ 2 ^ (2 * s - 3) := by
    have hypos : 0 < 2 ^ (s - 2) := pow_pos (by omega : 0 < 2) _
    have hfirst : 2 ^ (s - 1) = 2 * 2 ^ (s - 2) := by
      have hsucc : s - 1 = (s - 2) + 1 := by omega
      rw [hsucc, pow_add]
      ring
    have hbig : 2 ^ (2 * s - 3) = 2 ^ (s - 1) * 2 ^ (s - 2) := by
      rw [← pow_add]
      congr
      omega
    rw [hbig, hfirst]
    have hYge : 2 ≤ 2 ^ (s - 2) :=
      Nat.le_self_pow (n := s - 2) (by omega : s - 2 ≠ 0) 2
    nlinarith
  have hcast :
      ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) =
        ((2 ^ (2 * s - 3) : ℕ) : ℝ) - ((2 ^ (s - 1) : ℕ) : ℝ) -
          ((2 ^ (s - 2) : ℕ) : ℝ) + 1 := by
    have h1 : 2 ^ (s - 1) ≤ 2 ^ (2 * s - 3) := by
      exact le_trans (Nat.le_add_right _ _) hsmall_le_big_nat
    have h2 : 2 ^ (s - 2) ≤ 2 ^ (2 * s - 3) - 2 ^ (s - 1) := by
      omega
    norm_num [Nat.cast_sub h1, Nat.cast_sub h2]
  rw [hcast]
  have hsmall_le :
      ((2 ^ (s - 1) : ℕ) : ℝ) + ((2 ^ (s - 2) : ℕ) : ℝ) ≤
        rho * ((2 ^ (2 * s - 3) : ℕ) : ℝ) := by
    norm_num
    have hpow_pos : 0 ≤ (2 : ℝ) ^ (s - 2) := by positivity
    have hmul := mul_le_mul_of_nonneg_right hlarge hpow_pos
    calc
      (2 : ℝ) ^ (s - 1) + (2 : ℝ) ^ (s - 2)
          = 3 * (2 : ℝ) ^ (s - 2) := by
            have hsucc : s - 1 = (s - 2) + 1 := by omega
            rw [hsucc, pow_add]
            ring
      _ ≤ (rho * (2 : ℝ) ^ (s - 1)) * (2 : ℝ) ^ (s - 2) := by
            simpa [mul_assoc] using hmul
      _ = rho * (2 : ℝ) ^ (2 * s - 3) := by
            calc
              (rho * (2 : ℝ) ^ (s - 1)) * (2 : ℝ) ^ (s - 2)
                  = rho * ((2 : ℝ) ^ (s - 1) * (2 : ℝ) ^ (s - 2)) := by ring
              _ = rho * (2 : ℝ) ^ (2 * s - 3) := by
                    have hExp : s - 1 + (s - 2) = 2 * s - 3 := by omega
                    rw [← pow_add, hExp]
  calc
    (1 - rho) * (((2 ^ (2 * s - 3) : ℕ) : ℝ))
        = ((2 ^ (2 * s - 3) : ℕ) : ℝ) -
          rho * ((2 ^ (2 * s - 3) : ℕ) : ℝ) := by ring
    _ ≤ ((2 ^ (2 * s - 3) : ℕ) : ℝ) -
          (((2 ^ (s - 1) : ℕ) : ℝ) + ((2 ^ (s - 2) : ℕ) : ℝ)) := by
        linarith
    _ ≤ ((2 ^ (2 * s - 3) : ℕ) : ℝ) - ((2 ^ (s - 1) : ℕ) : ℝ) -
          ((2 ^ (s - 2) : ℕ) : ℝ) + 1 := by
        ring_nf
        norm_num
