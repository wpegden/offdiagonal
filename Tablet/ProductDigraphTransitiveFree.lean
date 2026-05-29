import Tablet.HsFreePair
import Tablet.ProductDigraph
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: ProductDigraphTransitiveFree]

universe u

theorem ProductDigraphTransitiveFree {V : Type u} (F G : LoopGraph V) (s : ℕ)
    [Fintype (ProductDigraphVertex F)]
    (hFG : HsFreePair F G s) :
    TransitiveTournamentFree (ProductDigraph F G) s := by
-- BODY
  sorry
