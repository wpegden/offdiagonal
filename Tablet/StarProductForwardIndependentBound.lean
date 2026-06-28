import Tablet.ExpanderMixingLemma
import Tablet.ForwardIndependentTupleCount
import Tablet.ForwardIndependentTupleCountSuccSnoc
import Tablet.MarkedTreePathCounting
import Tablet.PolarityGraphParameters
import Tablet.ProductDigraphVertex
import Tablet.StarProductConsistentTuple
import Tablet.StarProductDigraph
import Tablet.StarProductForwardIndependentChildCountLeVertices
import Tablet.StarProductForwardIndependentConsistentTuple
import Tablet.StarProductPolarityVertexCountBound

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
  sorry
