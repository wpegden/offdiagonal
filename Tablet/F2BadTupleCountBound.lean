import Tablet.F2BadTupleCountBoundNat

-- [TABLET NODE: F2BadTupleCountBound]

open Classical in
theorem F2BadTupleCountBound (p k : ℕ) (hk : 0 < k) :
    ((Fintype.card
        {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
          F2BadTuple p k ab} : ℕ) : ℝ) ≤
      Finset.sum (Finset.Icc 1 p)
        (fun t => ((Nat.choose k t : ℕ) : ℝ) *
          Real.rpow 2 (((p * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) := by
-- BODY
  classical
  let exp : ℕ → ℕ :=
    fun t => p * (t + k) - Nat.choose (t + 1) 2
  have hnat := F2BadTupleCountBoundNat p k hk
  have hreal :
      ((Fintype.card
          {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
            F2BadTuple p k ab} : ℕ) : ℝ) ≤
        ((Finset.sum (Finset.Icc 1 p)
          (fun t => Nat.choose k t * 2 ^ exp t) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hsum_cast :
      ((Finset.sum (Finset.Icc 1 p)
          (fun t => Nat.choose k t * 2 ^ exp t) : ℕ) : ℝ) =
        Finset.sum (Finset.Icc 1 p)
          (fun t => ((Nat.choose k t : ℕ) : ℝ) *
            Real.rpow 2 (((exp t : ℕ) : ℝ))) := by
    rw [Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro t ht
    simp [exp, Real.rpow_natCast]
  exact le_trans hreal (le_of_eq hsum_cast)
