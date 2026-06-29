import Tablet.ExpanderMixingLemma
import Tablet.ForwardIndependentTupleCount
import Tablet.ForwardIndependentTupleCountSuccSnoc
import Tablet.MarkedTreePathCounting
import Tablet.PolarityGraphParameters
import Tablet.ProductDigraphVertex
import Tablet.StarProductConsistentTuple
import Tablet.StarProductConcreteAllChildrenBound
import Tablet.StarProductConcreteMarkedChildrenBound
import Tablet.StarProductConcreteMarkedChildrenCertificate
import Tablet.StarProductConcretePathWeightBound
import Tablet.StarProductConcreteTreeCountingBound
import Tablet.StarProductConcretePathUnmarkedCertificate
import Tablet.StarProductConcreteUnmarkedPathNonempty
import Tablet.StarProductConcreteUnmarkedPathShrink
import Tablet.StarProductDigraph
import Tablet.StarProductExtensionOrthogonalToPrefixSpan
import Tablet.StarProductAbsorbedTreeCountingBound
import Tablet.StarProductFixedBExtensionBound
import Tablet.StarProductFixedBRankLeExtensionBound
import Tablet.StarProductForwardIndependentChildCountLeVertices
import Tablet.StarProductForwardIndependentConsistentTuple
import Tablet.StarProductDeltaPowerLeQPower
import Tablet.StarProductFinalNumericalAbsorption
import Tablet.StarProductFloorWeightSideConditions
import Tablet.StarProductFullRankNoForwardIndependentExtension
import Tablet.StarProductHLeDelta
import Tablet.StarProductLayerChoiceLe
import Tablet.StarProductLayerChoiceMax
import Tablet.StarProductLayerChoicePositive
import Tablet.StarProductLayerChoiceRealLowerBound
import Tablet.StarProductMarkedTreeCountingBridge
import Tablet.StarProductMarkedChildrenBound
import Tablet.StarProductPathUnmarkedBound
import Tablet.StarProductPathRankAtMostSizeMono
import Tablet.StarProductPoorChildrenBound
import Tablet.StarProductPoorExpanderMixingBound
import Tablet.StarProductPopularChildrenBound
import Tablet.StarProductPopularDoubleCountingBound
import Tablet.StarProductParameterChoice
import Tablet.StarProductPolarityVertexCountBound
import Tablet.StarProductQPowerLeTwoPow
import Tablet.StarProductShrinkCollapseForLaterExponents
import Tablet.StarProductShrinkThresholdCollapse
import Tablet.StarProductUnmarkedStepShrink
import Tablet.StarProductWLeK

-- [TABLET NODE: StarProductForwardIndependentBound]

universe u

theorem StarProductForwardIndependentBound (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [Fintype K]
        [Fintype (Projectivization K (Fin (t + 1) → K))]
        [Fintype (ProductDigraphVertex (PolarityGraph K t))],
        ∀ q : ℕ,
          q = Fintype.card K →
            ∀ k : ℕ,
              C ≤ (q : ℝ) →
                C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ) →
                  ((ForwardIndependentTupleCount
                    (StarProductDigraph (PolarityGraph K t)) k : ℕ) : ℝ) ≤
                    (C * (q : ℝ) ^ t) ^ k := by
-- BODY
  classical
  rcases StarProductParameterChoice t ht with
    ⟨A, C, hC_pos, hA_marked, hA_le_C, hC_absorb, hscale, hq_side⟩
  refine ⟨C, hC_pos, ?_⟩
  intro K _ _ _ _ q hq k hCq hk
  obtain ⟨_, _, _, _, _, hn, _, hd, _, _⟩ :=
    StarProductPolarityParameterBounds K t q ht hq
  rcases hq_side q hCq with ⟨hq_four, hlog_ge_one, hA_delta, hB_ge_one, hexp⟩
  exact
    StarProductAbsorbedTreeCountingBound K t q A k C ht hq hn hd
      hA_marked hA_delta hA_le_C hlog_ge_one hscale hC_absorb hB_ge_one
      hq_four hk hexp
