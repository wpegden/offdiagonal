import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductUnmarkedStepShrink]

universe u

theorem StarProductUnmarkedStepShrink {V : Type u} [DecidableEq V]
    (U U' Z good : Finset V) (t q : ℕ)
    (ht : 0 < (t : ℝ)) (hq : 0 < (q : ℝ))
    (hU'sub : U' ⊆ U) (hgoodsub : good ⊆ U)
    (hdisj : Disjoint U' good)
    (hgoodLower : (good.card : ℝ) ≥ (Z.card : ℝ) / (16 * (q : ℝ)))
    (hUle : (U.card : ℝ) ≤ 2 * (t : ℝ) * (Z.card : ℝ)) :
    (U'.card : ℝ) ≤ (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) * (U.card : ℝ) := by
-- BODY
  classical
  have hunion_sub : U' ∪ good ⊆ U := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx' | hxg
    · exact hU'sub hx'
    · exact hgoodsub hxg
  have hcard_sum_nat : U'.card + good.card ≤ U.card := by
    have hcard_union : (U' ∪ good).card = U'.card + good.card := by
      rw [Finset.card_union_of_disjoint hdisj]
    calc
      U'.card + good.card = (U' ∪ good).card := hcard_union.symm
      _ ≤ U.card := Finset.card_le_card hunion_sub
  have hcard_sum : (U'.card : ℝ) + (good.card : ℝ) ≤ (U.card : ℝ) := by
    exact_mod_cast hcard_sum_nat
  have hZ_to_U :
      (U.card : ℝ) / (32 * (t : ℝ) * (q : ℝ)) ≤
        (Z.card : ℝ) / (16 * (q : ℝ)) := by
    field_simp [ne_of_gt ht, ne_of_gt hq]
    nlinarith [hUle]
  calc
    (U'.card : ℝ) ≤ (U.card : ℝ) - (good.card : ℝ) := by
      linarith
    _ ≤ (U.card : ℝ) - (Z.card : ℝ) / (16 * (q : ℝ)) := by
      linarith
    _ ≤ (U.card : ℝ) - (U.card : ℝ) / (32 * (t : ℝ) * (q : ℝ)) := by
      linarith
    _ = (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) * (U.card : ℝ) := by
      ring
