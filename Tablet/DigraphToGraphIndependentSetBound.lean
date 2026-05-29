import Tablet.DigraphOrderedGraphCliqueFree
import Tablet.DigraphOrderedGraphIndependentSetBound

-- [TABLET NODE: DigraphToGraphIndependentSetBound]

universe u

theorem DigraphToGraphIndependentSetBound {W : Type u} [Fintype W]
    (D : Digraph W) (s k : ℕ)
    (hD : TransitiveTournamentFree D s) (hk : 1 ≤ k) :
    ∃ G : SimpleGraph W,
      (¬ ∃ S : Finset W, G.IsNClique s S) ∧
        ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) ≤
          (Real.exp 1 / (k : ℝ)) ^ k *
            ((ForwardIndependentTupleCount D k : ℕ) : ℝ) := by
-- BODY
  classical
  rcases DigraphOrderedGraphIndependentSetBound (D := D) (k := k) hk with ⟨r, hbound⟩
  refine ⟨DigraphOrderedGraph D r, ?_, hbound⟩
  exact DigraphOrderedGraphCliqueFree (D := D) (s := s) (r := r) hD
