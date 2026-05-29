import Tablet.DigraphOrderedGraph
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: DigraphOrderedGraphCliqueFree]

universe u

theorem DigraphOrderedGraphCliqueFree {W : Type u} [Fintype W]
    (D : Digraph W) (s : ℕ) (r : W → ℕ)
    (hD : TransitiveTournamentFree D s) :
    ¬ ∃ S : Finset W, (DigraphOrderedGraph D r).IsNClique s S := by
-- BODY
  sorry
