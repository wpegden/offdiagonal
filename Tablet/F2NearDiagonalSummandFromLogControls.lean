import Tablet.F2NearDiagonalExponentIdentity

-- [TABLET NODE: F2NearDiagonalSummandFromLogControls]

theorem F2NearDiagonalSummandFromLogControls (eps lambda : ℝ) (s a t : ℕ)
    (ht : t ∈ Finset.Icc 1 (s - 1))
    (hchoose :
      ((Nat.choose (s + a) t : ℕ) : ℝ) ≤
        Real.rpow 2 (((a : ℝ) + ((s - t : ℕ) : ℝ)) * lambda))
    (ha : (a : ℝ) * lambda ≤ eps * (s : ℝ) / 4)
    (hj :
      ((s - t : ℕ) : ℝ) * lambda +
        (3 / 2 : ℝ) * ((s - t : ℕ) : ℝ) - ((s - t : ℕ) : ℝ) ^ 2 / 2 ≤
          eps * (s : ℝ) / 4) :
    ((Nat.choose (s + a) t : ℕ) : ℝ) *
        Real.rpow 2
          ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ)) ≤
      Real.rpow 2
        ((s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
          (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) +
            eps * (s : ℝ) / 2) := by
-- BODY
  classical
  let j := s - t
  have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
  have htle : t ≤ s - 1 := (Finset.mem_Icc.mp ht).2
  have hj1 : 1 ≤ j := by
    dsimp [j]
    omega
  have hjs : j ≤ s - 1 := by
    dsimp [j]
    omega
  have hsub : s - j = t := by
    dsimp [j]
    omega
  have hexp_id :
      ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ)) =
        (s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
          (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) +
            (3 / 2 : ℝ) * (j : ℝ) - (j : ℝ) ^ 2 / 2 := by
    simpa [j, hsub] using F2NearDiagonalExponentIdentity s (s + a) j hj1 hjs
  let E : ℝ :=
    (s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
      (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) +
        (3 / 2 : ℝ) * (j : ℝ) - (j : ℝ) ^ 2 / 2
  let A : ℝ := ((a : ℝ) + (j : ℝ)) * lambda
  let B : ℝ :=
    (s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
      (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) +
        eps * (s : ℝ) / 2
  have hchoose' :
      ((Nat.choose (s + a) t : ℕ) : ℝ) ≤ Real.rpow 2 A := by
    simpa [A, j] using hchoose
  have hmul :
      ((Nat.choose (s + a) t : ℕ) : ℝ) * Real.rpow 2 E ≤
        Real.rpow 2 A * Real.rpow 2 E :=
    mul_le_mul_of_nonneg_right hchoose' (Real.rpow_nonneg (by norm_num) E)
  have hpow_add : Real.rpow 2 A * Real.rpow 2 E = Real.rpow 2 (A + E) :=
    (Real.rpow_add (by norm_num : (0 : ℝ) < 2) A E).symm
  have hAE_le_B : A + E ≤ B := by
    dsimp [A, E, B, j] at *
    norm_num at hchoose ha hj ⊢
    ring_nf at ha hj ⊢
    nlinarith
  calc
    ((Nat.choose (s + a) t : ℕ) : ℝ) *
        Real.rpow 2
          ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ))
        = ((Nat.choose (s + a) t : ℕ) : ℝ) * Real.rpow 2 E := by
          rw [hexp_id]
    _ ≤ Real.rpow 2 A * Real.rpow 2 E := hmul
    _ = Real.rpow 2 (A + E) := hpow_add
    _ ≤ Real.rpow 2 B :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hAE_le_B
    _ = Real.rpow 2
        ((s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
          (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) +
            eps * (s : ℝ) / 2) := by
          rfl
