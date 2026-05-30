import Tablet.Preamble

-- [TABLET NODE: F2ForwardIndependentSumBound]

theorem F2ForwardIndependentSumBound (s k : ℕ) (hs : 4 ≤ s) (hsk : s ≤ k) :
    Finset.sum (Finset.Icc 1 (s - 1))
      (fun t => ((Nat.choose k t : ℕ) : ℝ) *
        Real.rpow 2
          ((((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) ≤
      Real.rpow 2 ((s : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2) := by
-- BODY
  classical
  have choose_le :
      ∀ t : ℕ, 1 ≤ t → t ≤ s - 1 →
        Nat.choose (t + 1) 2 ≤ (s - 1) * (t + k) := by
    intro t ht1 htle
    rw [Nat.choose_two_right]
    apply Nat.div_le_of_le_mul
    have htle2 : t + 1 ≤ 2 * (s - 1) := by omega
    have hmul1 : (t + 1) * t ≤ (2 * (s - 1)) * t :=
      Nat.mul_le_mul_right t htle2
    have htk : t ≤ t + k := Nat.le_add_right t k
    have hmul2 : (2 * (s - 1)) * t ≤ (2 * (s - 1)) * (t + k) :=
      Nat.mul_le_mul_left (2 * (s - 1)) htk
    simpa [Nat.add_sub_cancel, mul_assoc, mul_left_comm, mul_comm] using hmul1.trans hmul2
  have choose_lower :
      ∀ t : ℕ, ((t : ℝ) ^ 2) / 2 ≤ (Nat.choose (t + 1) 2 : ℝ) := by
    intro t
    have hnat : t * t ≤ 2 * Nat.choose (t + 1) 2 := by
      rw [Nat.choose_two_right]
      rw [Nat.add_sub_cancel]
      have hdvd : 2 ∣ (t + 1) * t := by
        rw [← even_iff_two_dvd]
        simpa [mul_comm] using Nat.even_mul_succ_self t
      have hcancel : ((t + 1) * t) / 2 * 2 = (t + 1) * t :=
        Nat.div_mul_cancel hdvd
      nlinarith
    have hreal : ((t * t : ℕ) : ℝ) ≤ (2 * Nat.choose (t + 1) 2 : ℕ) := by
      exact_mod_cast hnat
    norm_num at hreal ⊢
    nlinarith
  have exponent_bound :
      ∀ t : ℕ, 1 ≤ t → t ≤ s - 1 →
        (((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ) ≤
          ((s - 1 : ℕ) : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2 := by
    intro t ht1 htle
    have hchoose_le := choose_le t ht1 htle
    have hchoose_lower := choose_lower t
    have hquad :
        ((s - 1 : ℕ) : ℝ) * (t : ℝ) - (t : ℝ) ^ 2 / 2 ≤ (s : ℝ) ^ 2 / 2 := by
      have hsminus_le : ((s - 1 : ℕ) : ℝ) ≤ (s : ℝ) := by
        exact_mod_cast Nat.sub_le s 1
      have ht_nonneg : 0 ≤ (t : ℝ) := by positivity
      have hmul_le :
          ((s - 1 : ℕ) : ℝ) * (t : ℝ) ≤ (s : ℝ) * (t : ℝ) :=
        mul_le_mul_of_nonneg_right hsminus_le ht_nonneg
      have hsq : 0 ≤ ((s : ℝ) - (t : ℝ)) ^ 2 := sq_nonneg _
      nlinarith
    calc
      (((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ)
          = (((s - 1) * (t + k) : ℕ) : ℝ) - (Nat.choose (t + 1) 2 : ℝ) := by
            exact Nat.cast_sub hchoose_le
      _ = ((s - 1 : ℕ) : ℝ) * (t : ℝ) + ((s - 1 : ℕ) : ℝ) * (k : ℝ) -
            (Nat.choose (t + 1) 2 : ℝ) := by
            norm_num
            ring
      _ ≤ ((s - 1 : ℕ) : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2 := by
            nlinarith
  have choose_sum_bound :
      (Finset.sum (Finset.Icc 1 (s - 1)) (fun t => Nat.choose k t) : ℕ) ≤ 2 ^ k := by
    have hsubset : Finset.Icc 1 (s - 1) ⊆ Finset.range (k + 1) := by
      intro t ht
      rw [Finset.mem_range]
      have htle : t ≤ s - 1 := (Finset.mem_Icc.mp ht).2
      omega
    have hle :
        (∑ t ∈ Finset.Icc 1 (s - 1), Nat.choose k t) ≤
          ∑ t ∈ Finset.range (k + 1), Nat.choose k t :=
      Finset.sum_le_sum_of_subset (f := Nat.choose k) hsubset
    have hle' :
        Finset.sum (Finset.Icc 1 (s - 1)) (fun t => Nat.choose k t) ≤
          Finset.sum (Finset.range (k + 1)) (fun t => Nat.choose k t) := by
      simpa using hle
    simpa [Nat.sum_range_choose] using hle'
  let A : ℝ := ((s - 1 : ℕ) : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2
  have hterm :
      ∀ t ∈ Finset.Icc 1 (s - 1),
        ((Nat.choose k t : ℕ) : ℝ) *
            Real.rpow 2
              ((((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ)) ≤
          ((Nat.choose k t : ℕ) : ℝ) * Real.rpow 2 A := by
    intro t ht
    have ht1 : 1 ≤ t := (Finset.mem_Icc.mp ht).1
    have htle : t ≤ s - 1 := (Finset.mem_Icc.mp ht).2
    have hexp :
        (((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ) ≤ A := by
      simpa [A] using exponent_bound t ht1 htle
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp)
      (by positivity)
  have hsum_terms :
      Finset.sum (Finset.Icc 1 (s - 1))
        (fun t => ((Nat.choose k t : ℕ) : ℝ) *
          Real.rpow 2
            ((((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) ≤
        Finset.sum (Finset.Icc 1 (s - 1))
          (fun t => ((Nat.choose k t : ℕ) : ℝ) * Real.rpow 2 A) := by
    exact Finset.sum_le_sum hterm
  have hchoose_sum_real :
      (Finset.sum (Finset.Icc 1 (s - 1))
          (fun t => ((Nat.choose k t : ℕ) : ℝ))) ≤ ((2 ^ k : ℕ) : ℝ) := by
    exact_mod_cast choose_sum_bound
  have hconst_nonneg : 0 ≤ Real.rpow 2 A := Real.rpow_nonneg (by norm_num) A
  have hsum_const :
      Finset.sum (Finset.Icc 1 (s - 1))
          (fun t => ((Nat.choose k t : ℕ) : ℝ) * Real.rpow 2 A) ≤
        ((2 ^ k : ℕ) : ℝ) * Real.rpow 2 A := by
    calc
      Finset.sum (Finset.Icc 1 (s - 1))
          (fun t => ((Nat.choose k t : ℕ) : ℝ) * Real.rpow 2 A)
          = (Finset.sum (Finset.Icc 1 (s - 1))
              (fun t => ((Nat.choose k t : ℕ) : ℝ))) * Real.rpow 2 A := by
            rw [Finset.sum_mul]
      _ ≤ ((2 ^ k : ℕ) : ℝ) * Real.rpow 2 A :=
            mul_le_mul_of_nonneg_right hchoose_sum_real hconst_nonneg
  calc
    Finset.sum (Finset.Icc 1 (s - 1))
      (fun t => ((Nat.choose k t : ℕ) : ℝ) *
        Real.rpow 2
          ((((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ)))
        ≤ Finset.sum (Finset.Icc 1 (s - 1))
          (fun t => ((Nat.choose k t : ℕ) : ℝ) * Real.rpow 2 A) := hsum_terms
    _ ≤ ((2 ^ k : ℕ) : ℝ) * Real.rpow 2 A := hsum_const
    _ = Real.rpow 2 ((s : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2) := by
      have hpow_nat : ((2 ^ k : ℕ) : ℝ) = Real.rpow 2 (k : ℝ) := by
        rw [Nat.cast_pow]
        exact (Real.rpow_natCast (2 : ℝ) k).symm
      rw [hpow_nat]
      change (2 : ℝ) ^ (k : ℝ) * (2 : ℝ) ^ A =
        (2 : ℝ) ^ ((s : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2)
      rw [← (Real.rpow_add (by norm_num : (0 : ℝ) < 2) (k : ℝ) A)]
      congr 1
      dsimp [A]
      rw [Nat.cast_sub (by omega : 1 ≤ s)]
      ring
