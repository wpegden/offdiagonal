import Mathlib.Algebra.Field.ZMod
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: F2CoordinateDigraphTransitiveFree]

universe u

theorem F2CoordinateDigraphTransitiveFree {p s : ℕ} (hps : p < s) {W : Type u}
    (x y : W → Fin p → ZMod 2)
    (hdiag : ∀ w : W, x w ⬝ᵥ y w = 1) :
    TransitiveTournamentFree (fun a b : W => x a ⬝ᵥ y b = 0) s := by
-- BODY
  rintro ⟨v, _hinj, hEdges⟩
  let yv : Fin s → Fin p → ZMod 2 := fun i => y (v i)
  have horth :
      ∀ i j : Fin s, i < j → x (v i) ⬝ᵥ yv j = 0 := by
    intro i j hij
    exact hEdges i j hij
  have hnonorth : ∀ i : Fin s, x (v i) ⬝ᵥ yv i ≠ 0 := by
    intro i hzero
    have hone : (1 : ZMod 2) = 0 := by
      rw [← hdiag (v i)]
      exact hzero
    exact one_ne_zero hone
  have hy_linearIndependent : LinearIndependent (ZMod 2) yv := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro c hsum i
    have hcoeff_by_val :
        ∀ n, ∀ i : Fin s, i.val = n → c i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro i hi
          have hprev : ∀ j : Fin s, j < i → c j = 0 := by
            intro j hji
            exact ih j.val (by
              show j.val < n
              rw [← hi]
              exact hji) j rfl
          have hdot_sum :
              (∑ j : Fin s, x (v i) ⬝ᵥ (c j • yv j)) = 0 := by
            calc
              (∑ j : Fin s, x (v i) ⬝ᵥ (c j • yv j))
                  = x (v i) ⬝ᵥ (∑ j : Fin s, c j • yv j) := by
                    simpa using
                      (dotProduct_sum (x (v i)) Finset.univ
                        (fun j : Fin s => c j • yv j)).symm
              _ = 0 := by
                    simp [hsum]
          have hsum_single :
              (∑ j : Fin s, x (v i) ⬝ᵥ (c j • yv j)) =
                c i * (x (v i) ⬝ᵥ yv i) := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hji
              by_cases hjlt : j < i
              · simp [hprev j hjlt]
              · have hilt : i < j := lt_of_le_of_ne (not_lt.mp hjlt) (Ne.symm hji)
                simp [dotProduct_smul, horth i j hilt]
            · intro hnot_mem
              simp at hnot_mem
          have hprod : c i * (x (v i) ⬝ᵥ yv i) = 0 := by
            exact hsum_single.symm.trans hdot_sum
          exact (mul_eq_zero.mp hprod).resolve_right (hnonorth i)
    exact hcoeff_by_val i.val i rfl
  have hcard_le :
      Fintype.card (Fin s) ≤ Module.finrank (ZMod 2) (Fin p → ZMod 2) :=
    hy_linearIndependent.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fin_fun] at hcard_le
  omega
