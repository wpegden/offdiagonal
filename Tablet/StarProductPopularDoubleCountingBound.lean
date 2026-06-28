import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductPopularDoubleCountingBound]

universe u

theorem StarProductPopularDoubleCountingBound {β γ : Type u} [DecidableEq β]
    [DecidableEq γ]
    (popular : Finset β) (Z : Finset γ) (W : γ → Finset β)
    (q ell : ℕ) (hq : 0 < (q : ℝ)) (hZpos : 0 < (Z.card : ℝ))
    (hpopular : ∀ b ∈ popular,
      ((Z.filter (fun y => b ∈ W y)).card : ℝ) ≥ (Z.card : ℝ) / (16 * (q : ℝ)))
    (hfiber : ∀ y ∈ Z,
      (((W y ∩ popular).card : ℝ) ≤ 2 * (q : ℝ) ^ ell / (q : ℝ))) :
    (popular.card : ℝ) ≤ 32 * (q : ℝ) ^ ell := by
-- BODY
  classical
  have hdouble :
      (∑ b ∈ popular, ((Z.filter (fun y => b ∈ W y)).card : ℝ)) =
        ∑ y ∈ Z, (((W y ∩ popular).card : ℝ)) := by
    calc
      (∑ b ∈ popular, ((Z.filter (fun y => b ∈ W y)).card : ℝ))
          = ∑ b ∈ popular, ∑ y ∈ Z, (if b ∈ W y then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro b hb
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro y hy
            by_cases hby : b ∈ W y <;> simp [hby]
      _ = ∑ y ∈ Z, ∑ b ∈ popular, (if b ∈ W y then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ y ∈ Z, (((popular.filter (fun b => b ∈ W y)).card : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            rw [Finset.card_filter, Nat.cast_sum]
            refine Finset.sum_congr rfl ?_
            intro b hb
            by_cases hby : b ∈ W y <;> simp [hby]
      _ = ∑ y ∈ Z, (((W y ∩ popular).card : ℝ)) := by
            refine Finset.sum_congr rfl ?_
            intro y hy
            have hset : popular.filter (fun b => b ∈ W y) = W y ∩ popular := by
              ext b
              simp [and_comm]
            rw [hset]
  have hlower :
      (popular.card : ℝ) * ((Z.card : ℝ) / (16 * (q : ℝ))) ≤
        ∑ b ∈ popular, ((Z.filter (fun y => b ∈ W y)).card : ℝ) := by
    calc
      (popular.card : ℝ) * ((Z.card : ℝ) / (16 * (q : ℝ)))
          = ∑ b ∈ popular, ((Z.card : ℝ) / (16 * (q : ℝ))) := by
              simp [Finset.sum_const, mul_comm]
      _ ≤ ∑ b ∈ popular, ((Z.filter (fun y => b ∈ W y)).card : ℝ) := by
              gcongr with b hb
              exact hpopular b hb
  have hupper :
      (∑ y ∈ Z, (((W y ∩ popular).card : ℝ))) ≤
        (Z.card : ℝ) * (2 * (q : ℝ) ^ ell / (q : ℝ)) := by
    calc
      (∑ y ∈ Z, (((W y ∩ popular).card : ℝ)))
          ≤ ∑ y ∈ Z, (2 * (q : ℝ) ^ ell / (q : ℝ)) := by
              gcongr with y hy
              exact hfiber y hy
      _ = (Z.card : ℝ) * (2 * (q : ℝ) ^ ell / (q : ℝ)) := by
              simp [Finset.sum_const, mul_comm]
  have hcombined :
      (popular.card : ℝ) * ((Z.card : ℝ) / (16 * (q : ℝ))) ≤
        (Z.card : ℝ) * (2 * (q : ℝ) ^ ell / (q : ℝ)) := by
    exact hlower.trans (by simpa [hdouble] using hupper)
  have hqne : (q : ℝ) ≠ 0 := ne_of_gt hq
  have hZne : (Z.card : ℝ) ≠ 0 := ne_of_gt hZpos
  field_simp [hqne, hZne] at hcombined ⊢
  nlinarith [hcombined]
