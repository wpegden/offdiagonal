import Mathlib.Combinatorics.Pigeonhole
import Mathlib.Tactic
import Tablet.StarProductIteratedShrink

-- [TABLET NODE: StarProductPathUnmarkedBound]

theorem StarProductPathUnmarkedBound
    (t m w : ℕ) (rho N : ℝ)
    (U : Fin (t + 1) → ℕ → ℝ)
    (unmarked : ℕ → Prop) [DecidablePred unmarked]
    (psi : ℕ → Fin (t + 1))
    (hrho_nonneg : 0 ≤ rho)
    (hinit : ∀ l, U l 0 ≤ N)
    (hshrink : ∀ i, i < m → unmarked (i + 1) →
      U (psi (i + 1)) (i + 1) ≤ rho * U (psi (i + 1)) i)
    (hmono : ∀ l i, i < m → ¬ (unmarked (i + 1) ∧ psi (i + 1) = l) →
      U l (i + 1) ≤ U l i)
    (hnonempty : ∀ i, i < m → unmarked (i + 1) →
      1 ≤ U (psi (i + 1)) i)
    (hcollapse : ∀ c, w / (t + 1) - 1 ≤ c → N * rho ^ c < 1) :
    ((Finset.Icc 1 m).filter unmarked).card ≤ w := by
-- BODY
  classical
  let S : Finset ℕ := (Finset.Icc 1 m).filter unmarked
  by_contra hnot
  have hgt : w < S.card := Nat.lt_of_not_ge hnot
  have hmul_le_w : Fintype.card (Fin (t + 1)) * (w / (t + 1)) ≤ w := by
    simp [Nat.mul_div_le]
  have hmul_lt : Fintype.card (Fin (t + 1)) * (w / (t + 1)) < S.card :=
    lt_of_le_of_lt hmul_le_w hgt
  rcases Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
      (s := S) (t := Finset.univ) (f := psi)
      (n := w / (t + 1)) (by simp) hmul_lt with
    ⟨l, _, hlarge⟩
  let Sl : Finset ℕ := S.filter fun i => psi i = l
  have hSl_card : w / (t + 1) < Sl.card := by
    simpa [Sl] using hlarge
  have hSl_nonempty : Sl.Nonempty := by
    exact Finset.card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hSl_card)
  let iStar : ℕ := Sl.max' hSl_nonempty
  have hiStar_mem_Sl : iStar ∈ Sl := Finset.max'_mem Sl hSl_nonempty
  have hiStar_mem_S : iStar ∈ S := (Finset.mem_filter.mp hiStar_mem_Sl).1
  have hiStar_psi : psi iStar = l := (Finset.mem_filter.mp hiStar_mem_Sl).2
  have hiStar_unmarked : unmarked iStar := (Finset.mem_filter.mp hiStar_mem_S).2
  have hiStar_range : iStar ∈ Finset.Icc 1 m := (Finset.mem_filter.mp hiStar_mem_S).1
  have hiStar_ge_one : 1 ≤ iStar := (Finset.mem_Icc.mp hiStar_range).1
  have hiStar_le_m : iStar ≤ m := (Finset.mem_Icc.mp hiStar_range).2
  let Earlier : Finset ℕ :=
    (Finset.Icc 1 (iStar - 1)).filter fun j => unmarked j ∧ psi j = l
  have herase_sub : Sl.erase iStar ⊆ Earlier := by
    intro j hj
    rw [Finset.mem_erase] at hj
    rcases hj with ⟨hj_ne, hjSl⟩
    have hjS : j ∈ S := (Finset.mem_filter.mp hjSl).1
    have hjpsi : psi j = l := (Finset.mem_filter.mp hjSl).2
    have hjunmarked : unmarked j := (Finset.mem_filter.mp hjS).2
    have hjrange : j ∈ Finset.Icc 1 m := (Finset.mem_filter.mp hjS).1
    have hj_ge_one : 1 ≤ j := (Finset.mem_Icc.mp hjrange).1
    have hj_le_iStar : j ≤ iStar := Finset.le_max' Sl j hjSl
    have hj_lt_iStar : j < iStar := lt_of_le_of_ne hj_le_iStar hj_ne
    have hj_le_pred : j ≤ iStar - 1 := Nat.le_sub_one_of_lt hj_lt_iStar
    simp [Earlier, hj_ge_one, hj_le_pred, hjunmarked, hjpsi]
  have hearly_card_lower : w / (t + 1) - 1 ≤ Earlier.card := by
    have h_erase_card :
        (Sl.erase iStar).card = Sl.card - 1 :=
      Finset.card_erase_of_mem hiStar_mem_Sl
    have h_erase_le : (Sl.erase iStar).card ≤ Earlier.card :=
      Finset.card_le_card herase_sub
    omega
  have hprefix :
      U l (iStar - 1) ≤ N * rho ^ Earlier.card := by
    have hiter := StarProductIteratedShrink
      m rho N (U l) (fun j => unmarked j ∧ psi j = l)
      hrho_nonneg (hinit l)
      (by
        intro i hi hsel
        rcases hsel with ⟨hu, hp⟩
        simpa [hp] using hshrink i hi hu)
      (by
        intro i hi hnot_sel
        exact hmono l i hi hnot_sel)
    have hpred_le_m : iStar - 1 ≤ m := by omega
    simpa [Earlier] using hiter (iStar - 1) hpred_le_m
  have hnon : 1 ≤ U l (iStar - 1) := by
    have hpred_lt_m : iStar - 1 < m := by omega
    have hstep_index : iStar - 1 + 1 = iStar := Nat.sub_add_cancel hiStar_ge_one
    have h := hnonempty (iStar - 1) hpred_lt_m (by simpa [hstep_index] using hiStar_unmarked)
    simpa [hstep_index, hiStar_psi] using h
  have hsmall : N * rho ^ Earlier.card < 1 :=
    hcollapse Earlier.card hearly_card_lower
  linarith
