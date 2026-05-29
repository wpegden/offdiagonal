import Tablet.LoopGraphAdjacencyAction
import Tablet.LoopGraphEdgeCountBetween

-- [TABLET NODE: LoopGraphEdgeCountBetweenAdjacencyIndicator]

universe u

open Classical in
theorem LoopGraphEdgeCountBetweenAdjacencyIndicator {V : Type u} [Fintype V]
    (G : LoopGraph V) (A B : Finset V) :
    ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) =
      ∑ a ∈ A, LoopGraphAdjacencyAction G
        (fun b : V => if b ∈ B then (1 : ℝ) else 0) a := by
-- BODY
  classical
  have h_edge_sum :
      LoopGraphEdgeCountBetween G A B =
        ∑ u ∈ A, LoopGraphEdgeCountBetween G ({u} : Finset V) B := by
    induction A using Finset.induction_on with
    | empty =>
        simp [LoopGraphEdgeCountBetween]
    | insert a A ha ih =>
        rw [Finset.sum_insert ha]
        rw [← ih]
        unfold LoopGraphEdgeCountBetween
        have hdisj :
            Disjoint
              (({a} ×ˢ B).filter (fun p : V × V => G p.1 p.2))
              ((A ×ˢ B).filter (fun p : V × V => G p.1 p.2)) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp1 hp2
          exact ha (by simpa [hp1.1.1] using hp2.1.1)
        have hfilter_eq :
            ((insert a A ×ˢ B).filter (fun p : V × V => G p.1 p.2)) =
              (({a} ×ˢ B).filter (fun p : V × V => G p.1 p.2)) ∪
                ((A ×ˢ B).filter (fun p : V × V => G p.1 p.2)) := by
          ext p
          constructor
          · intro hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
              Finset.mem_union, Finset.mem_singleton] at hp ⊢
            rcases hp.1.1 with hpa | hpA
            · exact Or.inl ⟨⟨hpa, hp.1.2⟩, hp.2⟩
            · exact Or.inr ⟨⟨hpA, hp.1.2⟩, hp.2⟩
          · intro hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
              Finset.mem_union, Finset.mem_singleton] at hp ⊢
            rcases hp with hp | hp
            · exact ⟨⟨Or.inl hp.1.1, hp.1.2⟩, hp.2⟩
            · exact ⟨⟨Or.inr hp.1.1, hp.1.2⟩, hp.2⟩
        change ((insert a A ×ˢ B).filter (fun p : V × V => G p.1 p.2)).card =
          (({a} ×ˢ B).filter (fun p : V × V => G p.1 p.2)).card +
            ((A ×ˢ B).filter (fun p : V × V => G p.1 p.2)).card
        rw [hfilter_eq, Finset.card_union_of_disjoint hdisj]
  have hsingle : ∀ a : V,
      ((LoopGraphEdgeCountBetween G ({a} : Finset V) B : ℕ) : ℝ) =
        LoopGraphAdjacencyAction G
          (fun b : V => if b ∈ B then (1 : ℝ) else 0) a := by
    intro a
    have hcard :
        (({a} ×ˢ B).filter (fun p : V × V => G p.1 p.2)).card =
          (B.filter (fun b : V => G a b)).card := by
      rw [Finset.singleton_product, Finset.filter_map, Finset.card_map]
      simp [Function.comp_def]
    have hsum :
        (∑ x : V, if G a x then if x ∈ B then (1 : ℝ) else 0 else 0) =
          ((B.filter (fun b : V => G a b)).card : ℝ) := by
      calc
        (∑ x : V, if G a x then if x ∈ B then (1 : ℝ) else 0 else 0)
            = ∑ x : V, if G a x ∧ x ∈ B then (1 : ℝ) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hxG : G a x <;> by_cases hxB : x ∈ B <;> simp [hxG, hxB]
        _ = ((B.filter (fun b : V => G a b)).card : ℝ) := by
              rw [Finset.sum_boole]
              have hfilter :
                  (Finset.univ.filter (fun x : V => G a x ∧ x ∈ B)) =
                    B.filter (fun x : V => G a x) := by
                ext x
                simp [and_comm]
              simp [hfilter]
    calc
      ((LoopGraphEdgeCountBetween G ({a} : Finset V) B : ℕ) : ℝ)
          = ((B.filter (fun b : V => G a b)).card : ℝ) := by
            change (((({a} ×ˢ B).filter
              (fun p : V × V => G p.1 p.2)).card : ℕ) : ℝ) =
                ((B.filter (fun b : V => G a b)).card : ℝ)
            exact_mod_cast hcard
      _ = LoopGraphAdjacencyAction G
          (fun b : V => if b ∈ B then (1 : ℝ) else 0) a := by
            rw [← hsum]
            simp [LoopGraphAdjacencyAction]
  calc
    ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ)
        = ∑ u ∈ A, ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ) := by
          rw [h_edge_sum]
          simp
    _ = ∑ a ∈ A, LoopGraphAdjacencyAction G
        (fun b : V => if b ∈ B then (1 : ℝ) else 0) a := by
          refine Finset.sum_congr rfl ?_
          intro a ha
          exact hsingle a
