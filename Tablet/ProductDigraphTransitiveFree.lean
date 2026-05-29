import Tablet.HsFreePair
import Tablet.ProductDigraph
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: ProductDigraphTransitiveFree]

universe u

theorem ProductDigraphTransitiveFree {V : Type u} (F G : LoopGraph V) (s : ℕ)
    (hFG : HsFreePair F G s) :
    TransitiveTournamentFree (ProductDigraph F G) s := by
-- BODY
  intro hT
  apply hFG
  rcases hT with ⟨v, _hv_inj, hArc⟩
  refine ⟨fun i => (v i).val.1, fun i => (v i).val.2, ?_, ?_⟩
  · intro i
    exact (v i).property
  · intro i j hij
    exact hArc i j hij
