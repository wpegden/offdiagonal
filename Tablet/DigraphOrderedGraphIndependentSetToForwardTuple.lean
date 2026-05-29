import Tablet.DigraphOrderedGraph
import Tablet.ForwardIndependentTuple

-- [TABLET NODE: DigraphOrderedGraphIndependentSetToForwardTuple]

universe u

theorem DigraphOrderedGraphIndependentSetToForwardTuple {W : Type u} [Fintype W]
    (D : Digraph W) (k : ℕ) (r : W → ℕ) (S : Finset W)
    (hS : (DigraphOrderedGraph D r)ᶜ.IsNClique k S)
    (hrinj : Set.InjOn r (↑S : Set W)) :
    ∃ v : Fin k → W,
      Function.Injective v ∧
        Set.range v = (↑S : Set W) ∧
          ForwardIndependentTuple D v := by
-- BODY
  classical
  have hcard : S.card = k := hS.card_eq
  have hClique : (DigraphOrderedGraph D r)ᶜ.IsClique (↑S : Set W) := hS.isClique
  let R : Finset ℕ := S.image r
  have hRcard : R.card = k := by
    simp [R, Finset.card_image_of_injOn hrinj, hcard]
  let rank : Fin k → ℕ := R.orderEmbOfFin hRcard
  have hrank_mem : ∀ i : Fin k, rank i ∈ R := by
    intro i
    dsimp [rank]
    exact Finset.orderEmbOfFin_mem R hRcard i
  have hpre : ∀ i : Fin k, ∃ w ∈ S, r w = rank i := by
    intro i
    have hi : rank i ∈ S.image r := by
      simpa [R] using hrank_mem i
    simpa using (Finset.mem_image.mp hi)
  let v : Fin k → W := fun i => Classical.choose (hpre i)
  have hv_mem : ∀ i : Fin k, v i ∈ S := by
    intro i
    exact (Classical.choose_spec (hpre i)).1
  have hv_rank : ∀ i : Fin k, r (v i) = rank i := by
    intro i
    exact (Classical.choose_spec (hpre i)).2
  have hv_inj : Function.Injective v := by
    intro i j hij
    apply (R.orderEmbOfFin hRcard).injective
    calc
      rank i = r (v i) := (hv_rank i).symm
      _ = r (v j) := by rw [hij]
      _ = rank j := hv_rank j
  refine ⟨v, hv_inj, ?_, ?_⟩
  · apply Set.ext
    intro x
    constructor
    · intro hx
      rcases hx with ⟨i, rfl⟩
      exact hv_mem i
    · intro hxS
      have hrx_mem : r x ∈ R := by
        exact Finset.mem_image.mpr ⟨x, hxS, rfl⟩
      have hrx_range : r x ∈ Set.range (R.orderEmbOfFin hRcard) := by
        rw [Finset.range_orderEmbOfFin R hRcard]
        exact hrx_mem
      rcases hrx_range with ⟨i, hi⟩
      refine ⟨i, ?_⟩
      apply hrinj (hv_mem i) hxS
      calc
        r (v i) = rank i := hv_rank i
        _ = r x := hi
  · intro i j hij hDij
    have hrank_lt : rank i < rank j :=
      (R.orderEmbOfFin hRcard).strictMono hij
    have hr_lt : r (v i) < r (v j) := by
      simpa [hv_rank] using hrank_lt
    have hne : v i ≠ v j := by
      intro hv
      exact (ne_of_lt hij) (hv_inj hv)
    have hcomp : (DigraphOrderedGraph D r)ᶜ.Adj (v i) (v j) :=
      hClique (hv_mem i) (hv_mem j) hne
    have hnot : ¬ (DigraphOrderedGraph D r).Adj (v i) (v j) := by
      simpa using hcomp.2
    exact hnot (Or.inl ⟨hr_lt, hDij⟩)
