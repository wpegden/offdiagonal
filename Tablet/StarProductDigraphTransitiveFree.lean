import Tablet.PolarityGraph
import Tablet.StarProductDigraph
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: StarProductDigraphTransitiveFree]

universe u

theorem StarProductDigraphTransitiveFree (K : Type u) [Field K] [Fintype K]
    (t : ℕ) (ht : 2 ≤ t) :
    TransitiveTournamentFree
      (StarProductDigraph (PolarityGraph K t)) (t + 1) := by
-- BODY
  sorry
