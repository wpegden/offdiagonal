import Tablet.HsFreePair
import Tablet.ForwardIndependentTupleCount
import Tablet.ProductDigraph
import Tablet.ProductDigraphShrinkingSequenceBound
import Tablet.ProductDigraphTransitiveFree
import Tablet.ProductDigraphVertex
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: ProductDigraphForwardIndependentBound]

universe u

theorem ProductDigraphForwardIndependentBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (s n dF dG : ℕ) (lambdaF lambdaG eta w : ℝ)
    (hs : 3 ≤ s) (hn : 3 ≤ n) (hdF : 0 < dF) (hdG : 0 < dG)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hFG : HsFreePair F G s)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (hw : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ))
    (heta_nonneg : 0 ≤ eta) (heta_le_one : eta ≤ 1) :
    ∃ (W : Type u) (_ : Fintype W), ∃ D : Digraph W,
      TransitiveTournamentFree D s ∧
        Fintype.card W = dF * n ∧
          ∀ k : ℕ, w ≤ (k : ℝ) →
            ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤
              (16 : ℝ) ^ k * Real.rpow eta ((k : ℝ) - w) *
                ((dF * n : ℕ) : ℝ) ^ k := by
-- BODY
  sorry
