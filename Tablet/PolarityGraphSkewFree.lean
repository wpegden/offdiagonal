import Tablet.NoSkewBipartiteConfiguration
import Tablet.PolarityGraph

-- [TABLET NODE: PolarityGraphSkewFree]

universe u

theorem PolarityGraphSkewFree (K : Type u) [Field K] (t : ℕ) :
    NoSkewBipartiteConfiguration (PolarityGraph K t) (t + 2) := by
-- BODY
  rintro ⟨a, b, hEdges, hDiag⟩
  let x : Fin (t + 2) → Fin (t + 1) → K := fun i => Projectivization.rep (a i)
  let y : Fin (t + 2) → Fin (t + 1) → K := fun i => Projectivization.rep (b i)
  have hx_ne : ∀ i, x i ≠ 0 := by
    intro i
    exact Projectivization.rep_nonzero (a i)
  have hy_ne : ∀ i, y i ≠ 0 := by
    intro i
    exact Projectivization.rep_nonzero (b i)
  have horth : ∀ i j : Fin (t + 2), i < j → x i ⬝ᵥ y j = 0 := by
    intro i j hij
    have h := hEdges i j hij
    change Projectivization.orthogonal (a i) (b j) at h
    have hmk :
        Projectivization.orthogonal
          (Projectivization.mk K (x i) (hx_ne i))
          (Projectivization.mk K (y j) (hy_ne j)) := by
      simpa [x, y, Projectivization.mk_rep] using h
    exact (Projectivization.orthogonal_mk (hx_ne i) (hy_ne j)).mp hmk
  have hnonorth : ∀ i : Fin (t + 2), x i ⬝ᵥ y i ≠ 0 := by
    intro i hzero
    have hmk :
        Projectivization.orthogonal
          (Projectivization.mk K (x i) (hx_ne i))
          (Projectivization.mk K (y i) (hy_ne i)) :=
      (Projectivization.orthogonal_mk (hx_ne i) (hy_ne i)).mpr hzero
    have hproj : Projectivization.orthogonal (a i) (b i) := by
      simpa [x, y, Projectivization.mk_rep] using hmk
    have hnot := hDiag i
    change ¬ Projectivization.orthogonal (a i) (b i) at hnot
    exact hnot hproj
  have hy_linearIndependent : LinearIndependent K y := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro c hsum i
    have hcoeff_by_val :
        ∀ n, ∀ i : Fin (t + 2), i.val = n → c i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro i hi
          have hprev : ∀ j : Fin (t + 2), j < i → c j = 0 := by
            intro j hji
            exact ih j.val (by
              show j.val < n
              rw [← hi]
              exact hji) j rfl
          have hdot_sum :
              (∑ j : Fin (t + 2), x i ⬝ᵥ (c j • y j)) = 0 := by
            calc
              (∑ j : Fin (t + 2), x i ⬝ᵥ (c j • y j))
                  = x i ⬝ᵥ (∑ j : Fin (t + 2), c j • y j) := by
                    simpa using
                      (dotProduct_sum (x i) Finset.univ
                        (fun j : Fin (t + 2) => c j • y j)).symm
              _ = 0 := by
                    simp [hsum]
          have hsum_single :
              (∑ j : Fin (t + 2), x i ⬝ᵥ (c j • y j)) =
                c i * (x i ⬝ᵥ y i) := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hji
              by_cases hjlt : j < i
              · simp [hprev j hjlt]
              · have hilt : i < j := lt_of_le_of_ne (not_lt.mp hjlt) (Ne.symm hji)
                simp [dotProduct_smul, horth i j hilt]
            · intro hnot_mem
              simp at hnot_mem
          have hprod : c i * (x i ⬝ᵥ y i) = 0 := by
            exact hsum_single.symm.trans hdot_sum
          exact (mul_eq_zero.mp hprod).resolve_right (hnonorth i)
    exact hcoeff_by_val i.val i rfl
  have hcard_le :
      Fintype.card (Fin (t + 2)) ≤ Module.finrank K (Fin (t + 1) → K) :=
    hy_linearIndependent.fintype_card_le_finrank
  rw [Fintype.card_fin, Module.finrank_fin_fun] at hcard_le
  omega
