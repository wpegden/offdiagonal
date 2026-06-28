import Tablet.ExpanderMixingLemma
import Tablet.ForwardIndependentTupleCount
import Tablet.MarkedTreePathCounting
import Tablet.PolarityGraphParameters
import Tablet.ProductDigraphVertex
import Tablet.StarProductConsistentTuple
import Tablet.StarProductDigraph

-- [TABLET NODE: StarProductForwardIndependentBound]

universe u

theorem StarProductForwardIndependentBound (K : Type u) [Field K] [Fintype K]
    (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K) :
    ∃ C : ℝ, 0 < C ∧
      ∀ k : ℕ,
        C ≤ (q : ℝ) →
          C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ) →
            ((ForwardIndependentTupleCount
              (StarProductDigraph (PolarityGraph K t)) k : ℕ) : ℝ) ≤
              (C * (q : ℝ) ^ t) ^ k := by
-- BODY
  sorry
