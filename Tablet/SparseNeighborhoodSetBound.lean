import Tablet.ExpanderMixingLemma

-- [TABLET NODE: SparseNeighborhoodSetBound]

universe u

theorem SparseNeighborhoodSetBound {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) (A B : Finset V)
    (hA : ∀ u : V, u ∈ A ↔
      ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ) ≤
        ((d : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ))) :
    (A.card : ℝ) * (B.card : ℝ) ≤
      (4 : ℝ) * lambda ^ 2 / (d : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
-- BODY
  sorry
