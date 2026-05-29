import Tablet.NoSkewBipartiteConfiguration
import Tablet.PolarityGraph

-- [TABLET NODE: PolarityGraphSkewFree]

universe u

theorem PolarityGraphSkewFree (K : Type u) [Field K] (t : ℕ) :
    NoSkewBipartiteConfiguration (PolarityGraph K t) (t + 2) := by
-- BODY
  sorry
