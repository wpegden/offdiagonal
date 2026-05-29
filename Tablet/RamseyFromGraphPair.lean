import Tablet.DigraphToGraphIndependentSetBound
import Tablet.ProductDigraphForwardIndependentBound
import Tablet.SamplingKsFreeRamseyBound

-- [TABLET NODE: RamseyFromGraphPair]

universe u

theorem RamseyFromGraphPair {V : Type u} [Fintype V]
    (F G : LoopGraph V) (s n dF dG k : ℕ) (lambdaF lambdaG eta w : ℝ)
    (hs : 3 ≤ s) (hn : 3 ≤ n) (hdG : 0 < dG) (hk : 1 ≤ k)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hFG : HsFreePair F G s)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (hw : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ))
    (heta_lower : 1 / (n : ℝ) ^ 2 ≤ eta) (heta_upper : eta ≤ 1) :
    ((w ≤ (k : ℝ) ∧ (k : ℝ) ≤ eta * (dF : ℝ) * (n : ℝ)) →
      (1 / 50 : ℝ) * (k : ℝ) *
          Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) - 1 ≤
        (RamseyNumber s k : ℝ)) ∧
      (((k : ℝ) ≤ eta * (dF : ℝ) * (n : ℝ) ∧
          (100 : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 / (dG : ℝ) ≤
            (k : ℝ)) →
        (k : ℝ) / (100 * eta) - 1 ≤ (RamseyNumber s k : ℝ)) := by
-- BODY
  sorry
