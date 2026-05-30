import Tablet.Preamble

-- [TABLET NODE: F2NearDiagonalSummationAbsorptionBound]

theorem F2NearDiagonalSummationAbsorptionBound (eps : ℝ) (s a : ℕ)
    (hs_pow : (s : ℝ) ≤ Real.rpow 2 (eps * (s : ℝ) / 2))
    (hterm :
      ∀ t ∈ Finset.Icc 1 (s - 1),
        ((Nat.choose (s + a) t : ℕ) : ℝ) *
            Real.rpow 2
              ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ)) ≤
          Real.rpow 2
            ((s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
              (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) +
                eps * (s : ℝ) / 2)) :
    Finset.sum (Finset.Icc 1 (s - 1))
      (fun t => ((Nat.choose (s + a) t : ℕ) : ℝ) *
        Real.rpow 2
          ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) ≤
      Real.rpow 2
        ((3 / 2 : ℝ) * (s : ℝ) ^ 2 + (a : ℝ) * (s : ℝ) -
          (5 / 2 : ℝ) * (s : ℝ) + eps * (s : ℝ)) := by
-- BODY
  classical
  let S := Finset.Icc 1 (s - 1)
  let E : ℝ :=
    (s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
      (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) + eps * (s : ℝ) / 2
  let F : ℝ :=
    (3 / 2 : ℝ) * (s : ℝ) ^ 2 + (a : ℝ) * (s : ℝ) -
      (5 / 2 : ℝ) * (s : ℝ) + eps * (s : ℝ)
  have hsum_terms :
      Finset.sum S
        (fun t => ((Nat.choose (s + a) t : ℕ) : ℝ) *
          Real.rpow 2
            ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) ≤
        Finset.sum S (fun _ => Real.rpow 2 E) := by
    apply Finset.sum_le_sum
    intro t ht
    simpa [S, E] using hterm t (by simpa [S] using ht)
  have hcard_nat : S.card ≤ s := by
    have hsubset : S ⊆ Finset.range s := by
      intro t ht
      have htmem : t ∈ Finset.Icc 1 (s - 1) := by simpa [S] using ht
      have ht1 : 1 ≤ t := (Finset.mem_Icc.mp htmem).1
      have htle : t ≤ s - 1 := (Finset.mem_Icc.mp htmem).2
      rw [Finset.mem_range]
      omega
    exact (Finset.card_le_card hsubset).trans_eq (Finset.card_range s)
  have hcard_real : (S.card : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hcard_nat
  have hsum_le :
      Finset.sum S
        (fun t => ((Nat.choose (s + a) t : ℕ) : ℝ) *
          Real.rpow 2
            ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) ≤
        (s : ℝ) * Real.rpow 2 E := by
    calc
      Finset.sum S
        (fun t => ((Nat.choose (s + a) t : ℕ) : ℝ) *
          Real.rpow 2
            ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ)))
          ≤ Finset.sum S (fun _ => Real.rpow 2 E) := hsum_terms
      _ = (S.card : ℝ) * Real.rpow 2 E := by simp
      _ ≤ (s : ℝ) * Real.rpow 2 E :=
        mul_le_mul_of_nonneg_right hcard_real (Real.rpow_nonneg (by norm_num) E)
  have hmul_absorb :
      (s : ℝ) * Real.rpow 2 E ≤ Real.rpow 2 (eps * (s : ℝ) / 2) * Real.rpow 2 E :=
    mul_le_mul_of_nonneg_right hs_pow (Real.rpow_nonneg (by norm_num) E)
  have hpow_mul :
      Real.rpow 2 (eps * (s : ℝ) / 2) * Real.rpow 2 E =
        Real.rpow 2 (E + eps * (s : ℝ) / 2) := by
    rw [mul_comm]
    exact (Real.rpow_add (by norm_num : (0 : ℝ) < 2) E (eps * (s : ℝ) / 2)).symm
  have hE_le_F : E + eps * (s : ℝ) / 2 ≤ F := by
    dsimp [E, F]
    norm_num
    ring_nf
    nlinarith [show (0 : ℝ) ≤ (a : ℝ) by positivity]
  calc
    Finset.sum (Finset.Icc 1 (s - 1))
      (fun t => ((Nat.choose (s + a) t : ℕ) : ℝ) *
        Real.rpow 2
          ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ)))
        = Finset.sum S
            (fun t => ((Nat.choose (s + a) t : ℕ) : ℝ) *
              Real.rpow 2
                ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) := by
          rfl
    _ ≤ (s : ℝ) * Real.rpow 2 E := hsum_le
    _ ≤ Real.rpow 2 (eps * (s : ℝ) / 2) * Real.rpow 2 E := hmul_absorb
    _ = Real.rpow 2 (E + eps * (s : ℝ) / 2) := hpow_mul
    _ ≤ Real.rpow 2 F :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hE_le_F
    _ = Real.rpow 2
        ((3 / 2 : ℝ) * (s : ℝ) ^ 2 + (a : ℝ) * (s : ℝ) -
          (5 / 2 : ℝ) * (s : ℝ) + eps * (s : ℝ)) := by
          rfl
