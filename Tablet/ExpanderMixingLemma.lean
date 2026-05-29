import Tablet.LoopGraphEdgeCountBetween
import Tablet.LoopGraphNdLambda

-- [TABLET NODE: ExpanderMixingLemma]

universe u

theorem ExpanderMixingLemma {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) (A B : Finset V) :
    |((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) -
      ((d : ℝ) / (n : ℝ)) * (A.card : ℝ) * (B.card : ℝ)| ≤
        lambda * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
-- BODY
  sorry
