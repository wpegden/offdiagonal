import Tablet.DigraphOrderedGraph
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: DigraphOrderedGraphCliqueFree]

universe u

theorem DigraphOrderedGraphCliqueFree {W : Type u} [Fintype W]
    (D : Digraph W) (s : ℕ) (r : W → ℕ)
    (hD : TransitiveTournamentFree D s) :
    ¬ ∃ S : Finset W, (DigraphOrderedGraph D r).IsNClique s S := by
-- BODY
  classical
  rintro ⟨S, hS⟩
  have hcard : S.card = s := hS.card_eq
  have hClique : (DigraphOrderedGraph D r).IsClique (↑S : Set W) := hS.isClique
  have hinjOn : Set.InjOn r (↑S : Set W) := by
    intro u hu v hv hruv
    by_contra huv
    have hadj : (DigraphOrderedGraph D r).Adj u v := hClique hu hv huv
    simp [DigraphOrderedGraph, hruv] at hadj
  let R : Finset ℕ := S.image r
  have hRcard : R.card = s := by
    simp [R, Finset.card_image_of_injOn hinjOn, hcard]
  let rank : Fin s → ℕ := R.orderEmbOfFin hRcard
  have hrank_mem : ∀ i : Fin s, rank i ∈ R := by
    intro i
    dsimp [rank]
    rw [Finset.orderEmbOfFin_apply]
    apply (Finset.mem_sort (s := R) (r := fun a b : ℕ => a ≤ b)).mp
    have hi_len : i.1 < (R.sort (fun a b : ℕ => a ≤ b)).length := by
      simpa [Finset.length_sort, hRcard] using i.2
    simpa using
      (List.get_mem (l := R.sort (fun a b : ℕ => a ≤ b)) ⟨i.1, hi_len⟩)
  have hpre : ∀ i : Fin s, ∃ w ∈ S, r w = rank i := by
    intro i
    have hi : rank i ∈ S.image r := by
      simpa [R] using hrank_mem i
    simpa using (Finset.mem_image.mp hi)
  let v : Fin s → W := fun i => Classical.choose (hpre i)
  have hv_mem : ∀ i : Fin s, v i ∈ S := by
    intro i
    exact (Classical.choose_spec (hpre i)).1
  have hv_rank : ∀ i : Fin s, r (v i) = rank i := by
    intro i
    exact (Classical.choose_spec (hpre i)).2
  have hv_inj : Function.Injective v := by
    intro i j hij
    apply (R.orderEmbOfFin hRcard).injective
    calc
      rank i = r (v i) := (hv_rank i).symm
      _ = r (v j) := by rw [hij]
      _ = rank j := hv_rank j
  apply hD
  refine ⟨v, hv_inj, ?_⟩
  intro i j hij
  have hrank_lt : rank i < rank j :=
    (R.orderEmbOfFin hRcard).strictMono hij
  have hne : v i ≠ v j := by
    intro hv
    exact (ne_of_lt hij) (hv_inj hv)
  have hadj : (DigraphOrderedGraph D r).Adj (v i) (v j) :=
    hClique (hv_mem i) (hv_mem j) hne
  have hr_lt : r (v i) < r (v j) := by
    simpa [hv_rank] using hrank_lt
  rcases hadj with hforward | hbackward
  · exact hforward.2
  · exact False.elim ((not_lt_of_gt hr_lt) hbackward.1)
