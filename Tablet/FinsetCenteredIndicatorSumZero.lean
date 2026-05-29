import Tablet.Preamble

-- [TABLET NODE: FinsetCenteredIndicatorSumZero]

universe u

open Classical in
theorem FinsetCenteredIndicatorSumZero {V : Type u} [Fintype V]
    (A : Finset V) (hn : ((Fintype.card V : ℕ) : ℝ) ≠ 0) :
    (∑ v : V, ((if v ∈ A then (1 : ℝ) else 0) -
      (A.card : ℝ) / (Fintype.card V : ℝ))) = 0 := by
-- BODY
  have hsum_indicator :
      (∑ v : V, if v ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
    rw [Finset.sum_boole (fun v : V => v ∈ A) Finset.univ]
    have hfilter :
        (Finset.univ.filter (fun v : V => v ∈ A)) = A := by
      ext v
      simp
    simp [hfilter]
  calc
    (∑ v : V, ((if v ∈ A then (1 : ℝ) else 0) -
      (A.card : ℝ) / (Fintype.card V : ℝ)))
        = (∑ v : V, if v ∈ A then (1 : ℝ) else 0) -
            ∑ v : V, ((A.card : ℝ) / (Fintype.card V : ℝ)) := by
          rw [Finset.sum_sub_distrib]
    _ = (A.card : ℝ) - (Fintype.card V : ℝ) *
          ((A.card : ℝ) / (Fintype.card V : ℝ)) := by
          simp [hsum_indicator, Finset.sum_const, nsmul_eq_mul]
    _ = 0 := by
          field_simp [hn]
          ring
