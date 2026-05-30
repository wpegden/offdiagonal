import Tablet.CloseToDiagonalVertexCountLowerBound

-- [TABLET NODE: LinearOffDiagonalVertexCountDominates]

open Filter in
theorem LinearOffDiagonalVertexCountDominates (C : ℝ) (hC : 1 < C) :
    ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) ≤
        ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) := by
-- BODY
  rcases CloseToDiagonalVertexCountLowerBound (1 / 2 : ℝ) (by norm_num) with
    ⟨sN, _hsN4, hN⟩
  refine ⟨max sN 8, ?_⟩
  intro s hs
  let alpha : ℝ := (1 - 1 / (2 * C)) * (s : ℝ)
  let A : ℝ := ((2 ^ (2 * s - 3) : ℕ) : ℝ)
  let N : ℝ := ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ)
  have hsN : sN ≤ s := le_trans (Nat.le_max_left sN 8) hs
  have hs8 : 8 ≤ s := le_trans (Nat.le_max_right sN 8) hs
  have hCpos : 0 < C := lt_trans (by norm_num) hC
  have h2Cpos : 0 < 2 * C := by positivity
  have hcoef_le_one : 1 - 1 / (2 * C) ≤ 1 := by
    have hfrac_nonneg : 0 ≤ 1 / (2 * C) := by positivity
    linarith
  have halpha_le_s : alpha ≤ (s : ℝ) := by
    dsimp [alpha]
    exact (mul_le_mul_of_nonneg_right hcoef_le_one (by positivity : 0 ≤ (s : ℝ))).trans_eq
      (by ring)
  have htarget_le_two_s :
      Real.rpow 2 alpha ≤ Real.rpow 2 (s : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) halpha_le_s
  have hs_exp_le : (s : ℝ) ≤ 2 * (s : ℝ) - 4 := by
    nlinarith [show (8 : ℝ) ≤ (s : ℝ) by exact_mod_cast hs8]
  have htwo_s_le_Ahalf :
      Real.rpow 2 (s : ℝ) ≤ (1 / 2 : ℝ) * A := by
    have hpow_le :
        Real.rpow 2 (s : ℝ) ≤ Real.rpow 2 (2 * (s : ℝ) - 4) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hs_exp_le
    have hAhalf_eq :
        (1 / 2 : ℝ) * A = Real.rpow 2 (2 * (s : ℝ) - 4) := by
      dsimp [A]
      have hA_eq : ((2 ^ (2 * s - 3) : ℕ) : ℝ) = Real.rpow 2 (2 * (s : ℝ) - 3) := by
        have hsub : ((2 * s - 3 : ℕ) : ℝ) = 2 * (s : ℝ) - 3 := by
          norm_num [Nat.cast_sub (by omega : 3 ≤ 2 * s)]
        rw [← hsub]
        norm_num
      rw [hA_eq]
      change (1 / 2 : ℝ) * (2 : ℝ) ^ (2 * (s : ℝ) - 3) =
        (2 : ℝ) ^ (2 * (s : ℝ) - 4)
      have hhalf : (1 / 2 : ℝ) = (2 : ℝ) ^ (-1 : ℝ) := by
        rw [Real.rpow_neg_one]
        norm_num
      rw [hhalf]
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      congr 1
      ring_nf
    exact hpow_le.trans_eq hAhalf_eq.symm
  have hNlower : (1 / 2 : ℝ) * A ≤ N := by
    have h := hN s hsN
    norm_num at h ⊢
    simpa [A, N] using h
  calc
    Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ))
        = Real.rpow 2 alpha := by rfl
    _ ≤ Real.rpow 2 (s : ℝ) := htarget_le_two_s
    _ ≤ (1 / 2 : ℝ) * A := htwo_s_le_Ahalf
    _ ≤ N := hNlower
