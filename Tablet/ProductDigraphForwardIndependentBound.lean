import Tablet.HsFreePair
import Tablet.ProductDigraph
import Tablet.ProductDigraphShrinkingSequenceBound
import Tablet.ProductDigraphTransitiveFree
import Tablet.ProductDigraphVertex
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: ProductDigraphForwardIndependentBound]

universe u

theorem ProductDigraphForwardIndependentBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (s n dF dG : ℕ) (lambdaF lambdaG eta w : ℝ)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hFG : HsFreePair F G s)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (hw : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ)) :
    ∃ (W : Type u) (_ : Fintype W), ∃ D : Digraph W,
      TransitiveTournamentFree D s ∧
        Fintype.card W = dF * n ∧
          ∀ k : ℕ, w ≤ (k : ℝ) →
            ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤
              (16 : ℝ) ^ k * Real.rpow eta ((k : ℝ) - w) *
                ((dF * n : ℕ) : ℝ) ^ k := by
-- BODY
  sorry
