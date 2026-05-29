import Tablet.BinarySequenceWeight
import Tablet.ProductDigraphFixedSequenceTupleCount
import Tablet.SparseNeighborhoodSetBound

-- [TABLET NODE: ProductDigraphShrinkingSequenceBound]

universe u

theorem ProductDigraphShrinkingSequenceBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (n dF dG t : ℕ) (lambdaF lambdaG eta : ℝ)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (z : Fin t → Bool) :
    ((ProductDigraphFixedSequenceTupleCount F G n dG t z : ℕ) : ℝ) ≤
      ((8 : ℝ) * eta) ^ (t - BinarySequenceWeight z) *
        ((dF * n : ℕ) : ℝ) ^ t := by
-- BODY
  sorry
