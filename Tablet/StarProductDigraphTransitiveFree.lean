import Tablet.PolarityGraph
import Tablet.StarProductDigraph
import Tablet.TransitiveTournamentFree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

-- [TABLET NODE: StarProductDigraphTransitiveFree]

universe u

theorem StarProductDigraphTransitiveFree (K : Type u) [Field K] [Fintype K]
    (t : ℕ) (ht : 2 ≤ t) :
    TransitiveTournamentFree
      (StarProductDigraph (PolarityGraph K t)) (t + 1) := by
-- BODY
  classical
  have _ht : 2 ≤ t := ht
  unfold TransitiveTournamentFree
  rintro ⟨v, hv_inj, hv_arc⟩
  let P := Projectivization K (Fin (t + 1) → K)
  let a : Fin (t + 1) → P := fun i => (v i).val.1
  let b : Fin (t + 1) → P := fun i => (v i).val.2
  let x : Fin (t + 1) → Fin (t + 1) → K := fun i => Projectivization.rep (a i)
  let y : Fin (t + 1) → Fin (t + 1) → K := fun i => Projectivization.rep (b i)
  have hx_ne : ∀ i, x i ≠ 0 := by
    intro i
    exact Projectivization.rep_nonzero (a i)
  have hy_ne : ∀ i, y i ≠ 0 := by
    intro i
    exact Projectivization.rep_nonzero (b i)
  have hdiag : ∀ i : Fin (t + 1), x i ⬝ᵥ y i = 0 := by
    intro i
    have h := (v i).property
    change Projectivization.orthogonal (a i) (b i) at h
    have hmk :
        Projectivization.orthogonal
          (Projectivization.mk K (x i) (hx_ne i))
          (Projectivization.mk K (y i) (hy_ne i)) := by
      simpa [x, y, Projectivization.mk_rep] using h
    exact (Projectivization.orthogonal_mk (hx_ne i) (hy_ne i)).mp hmk
  have horth : ∀ i j : Fin (t + 1), i < j → x i ⬝ᵥ y j = 0 := by
    intro i j hij
    have h := (hv_arc i j hij).1
    change Projectivization.orthogonal (a i) (b j) at h
    have hmk :
        Projectivization.orthogonal
          (Projectivization.mk K (x i) (hx_ne i))
          (Projectivization.mk K (y j) (hy_ne j)) := by
      simpa [x, y, Projectivization.mk_rep] using h
    exact (Projectivization.orthogonal_mk (hx_ne i) (hy_ne j)).mp hmk
  have hnonorth :
      ∀ i j : Fin (t + 1), i < j → x j ⬝ᵥ y i ≠ 0 := by
    intro i j hij hzero
    have hnot := (hv_arc i j hij).2
    change ¬ Projectivization.orthogonal (a j) (b i) at hnot
    have hmk :
        Projectivization.orthogonal
          (Projectivization.mk K (x j) (hx_ne j))
          (Projectivization.mk K (y i) (hy_ne i)) :=
      (Projectivization.orthogonal_mk (hx_ne j) (hy_ne i)).mpr hzero
    have hproj : Projectivization.orthogonal (a j) (b i) := by
      simpa [x, y, Projectivization.mk_rep] using hmk
    exact hnot hproj
  have hz_exists : ∃ z : Fin (t + 1) → K, z ⬝ᵥ y (Fin.last t) ≠ 0 := by
    have hnotforall : ¬ ∀ z : Fin (t + 1) → K, y (Fin.last t) ⬝ᵥ z = 0 := by
      intro hzero
      exact hy_ne (Fin.last t) ((dotProduct_eq_zero_iff).mp hzero)
    obtain ⟨z, hz⟩ := not_forall.mp hnotforall
    exact ⟨z, by simpa [dotProduct_comm] using hz⟩
  obtain ⟨z, hz⟩ := hz_exists
  have hy_linearIndependent : LinearIndependent K y := by
    refine Fintype.linearIndependent_iff.mpr ?_
    intro c hsum i
    have hcoeff_by_val :
        ∀ n, ∀ i : Fin (t + 1), i.val = n → c i = 0 := by
      intro n
      induction n using Nat.strong_induction_on with
      | h n ih =>
          intro i hi
          have hprev : ∀ j : Fin (t + 1), j < i → c j = 0 := by
            intro j hji
            exact ih j.val (by
              show j.val < n
              rw [← hi]
              exact hji) j rfl
          let w : Fin (t + 1) → K :=
            if hlast : i.val = t then z
            else x ⟨i.val + 1, by omega⟩
          have hw_nonorth : w ⬝ᵥ y i ≠ 0 := by
            dsimp [w]
            split_ifs with hlast
            · have hi_last : i = Fin.last t := by
                ext
                simp [hlast]
              simpa [hi_last] using hz
            · have hsucc : i < (⟨i.val + 1, by omega⟩ : Fin (t + 1)) := by
                change i.val < i.val + 1
                omega
              exact hnonorth i ⟨i.val + 1, by omega⟩ hsucc
          have hw_orth_later : ∀ j : Fin (t + 1), i < j → w ⬝ᵥ y j = 0 := by
            intro j hij
            dsimp [w]
            split_ifs with hlast
            · have : False := by
                rw [Fin.lt_def] at hij
                omega
              exact this.elim
            · let ip1 : Fin (t + 1) := ⟨i.val + 1, by omega⟩
              by_cases hji : j.val = i.val + 1
              · have hj : j = ip1 := by
                  ext
                  exact hji
                simpa [ip1, hj] using hdiag ip1
              · have hip1j : ip1 < j := by
                  change i.val + 1 < j.val
                  rw [Fin.lt_def] at hij
                  omega
                exact horth ip1 j hip1j
          have hdot_sum :
              (∑ j : Fin (t + 1), w ⬝ᵥ (c j • y j)) = 0 := by
            calc
              (∑ j : Fin (t + 1), w ⬝ᵥ (c j • y j))
                  = w ⬝ᵥ (∑ j : Fin (t + 1), c j • y j) := by
                    simpa using
                      (dotProduct_sum w Finset.univ
                        (fun j : Fin (t + 1) => c j • y j)).symm
              _ = 0 := by
                    simp [hsum]
          have hsum_single :
              (∑ j : Fin (t + 1), w ⬝ᵥ (c j • y j)) =
                c i * (w ⬝ᵥ y i) := by
            rw [Finset.sum_eq_single i]
            · simp
            · intro j _ hji
              by_cases hjlt : j < i
              · simp [hprev j hjlt]
              · have hilt : i < j := lt_of_le_of_ne (not_lt.mp hjlt) (Ne.symm hji)
                simp [dotProduct_smul, hw_orth_later j hilt]
            · intro hnot_mem
              simp at hnot_mem
          have hprod : c i * (w ⬝ᵥ y i) = 0 := by
            exact hsum_single.symm.trans hdot_sum
          exact (mul_eq_zero.mp hprod).resolve_right hw_nonorth
    exact hcoeff_by_val i.val i rfl
  let B : Module.Basis (Fin (t + 1)) K (Fin (t + 1) → K) :=
    basisOfPiSpaceOfLinearIndependent hy_linearIndependent
  have hB_eq : ⇑B = y := by
    exact coe_basisOfPiSpaceOfLinearIndependent hy_linearIndependent
  have hx0_y : ∀ j : Fin (t + 1), x 0 ⬝ᵥ y j = 0 := by
    intro j
    by_cases hj : j = 0
    · simpa [hj] using hdiag (0 : Fin (t + 1))
    · have h0j : (0 : Fin (t + 1)) < j := by
        rw [Fin.lt_def]
        exact Nat.pos_of_ne_zero (by
          intro hval
          exact hj (Fin.ext hval))
      exact horth 0 j h0j
  have hx0_all : ∀ w : Fin (t + 1) → K, x 0 ⬝ᵥ w = 0 := by
    intro w
    rw [← B.sum_repr w]
    simp [dotProduct_sum, dotProduct_smul, hB_eq, hx0_y]
  have hx0_zero : x 0 = 0 := (dotProduct_eq_zero_iff).mp hx0_all
  exact hx_ne 0 hx0_zero
