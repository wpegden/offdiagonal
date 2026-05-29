import Tablet.Preamble

-- [TABLET NODE: FinsetCenteredIndicatorNormSqLeCard]

universe u

open Classical in
theorem FinsetCenteredIndicatorNormSqLeCard {V : Type u} [Fintype V]
    (A : Finset V) (hn : ((Fintype.card V : ℕ) : ℝ) ≠ 0) :
    (∑ v : V, (((if v ∈ A then (1 : ℝ) else 0) -
      (A.card : ℝ) / (Fintype.card V : ℝ)) ^ 2)) ≤ (A.card : ℝ) := by
-- BODY
  let c : ℝ := (A.card : ℝ) / (Fintype.card V : ℝ)
  have hsum_indicator :
      (∑ v : V, if v ∈ A then (1 : ℝ) else 0) = (A.card : ℝ) := by
    rw [Finset.sum_boole (fun v : V => v ∈ A) Finset.univ]
    have hfilter :
        (Finset.univ.filter (fun v : V => v ∈ A)) = A := by
      ext v
      simp
    simp [hfilter]
  have hsum_formula :
      (∑ v : V, (((if v ∈ A then (1 : ℝ) else 0) -
        (A.card : ℝ) / (Fintype.card V : ℝ)) ^ 2)) =
        (A.card : ℝ) - (A.card : ℝ) ^ 2 / (Fintype.card V : ℝ) := by
    calc
      (∑ v : V, (((if v ∈ A then (1 : ℝ) else 0) -
        (A.card : ℝ) / (Fintype.card V : ℝ)) ^ 2))
          = ∑ v : V, ((if v ∈ A then (1 : ℝ) else 0) ^ 2 -
              2 * c * (if v ∈ A then (1 : ℝ) else 0) + c ^ 2) := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            dsimp [c]
            ring
      _ = (A.card : ℝ) - 2 * c * (A.card : ℝ) +
            (Fintype.card V : ℝ) * c ^ 2 := by
            simp [Finset.sum_add_distrib, Finset.sum_sub_distrib,
              hsum_indicator, Finset.sum_const, nsmul_eq_mul, mul_assoc]
            ring
      _ = (A.card : ℝ) - (A.card : ℝ) ^ 2 / (Fintype.card V : ℝ) := by
            dsimp [c]
            field_simp [hn]
            ring
  rw [hsum_formula]
  have hnonneg : 0 ≤ (A.card : ℝ) ^ 2 / (Fintype.card V : ℝ) := by
    have hcard_pos : 0 < (Fintype.card V : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero (by
        intro h
        apply hn
        exact_mod_cast h)
    positivity
  linarith
