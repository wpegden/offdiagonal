import Tablet.ForwardIndependentTuple
import Tablet.ProductDigraphVertex
import Tablet.StarProductConsistentTuple
import Tablet.StarProductDigraph

-- [TABLET NODE: StarProductForwardIndependentConsistentTuple]

universe u

theorem StarProductForwardIndependentConsistentTuple {V : Type u}
    (G : LoopGraph V) {k : ℕ} (v : Fin k → ProductDigraphVertex G) :
    ForwardIndependentTuple (StarProductDigraph G) v ↔
      StarProductConsistentTuple G (fun i => (v i).val.1) (fun i => (v i).val.2) := by
-- BODY
  constructor
  · intro hfi
    constructor
    · intro i
      exact (v i).property
    · intro i j hij hij_edge
      by_contra hnot
      exact hfi i j hij ⟨hij_edge, hnot⟩
  · intro hcons i j hij harc
    exact harc.2 (hcons.2 i j hij harc.1)
