import Tablet.ForwardIndependentTuple
import Tablet.StarProductMarkedTupleSignature

-- [TABLET NODE: StarProductMarkedTupleFiberCount]

universe u

noncomputable def StarProductMarkedTupleFiberCount {V : Type u}
    (G : LoopGraph V) [Fintype (ProductDigraphVertex G)] {k : ℕ}
    (marked : ∀ m : ℕ, (Fin m → ProductDigraphVertex G) → ProductDigraphVertex G → Bool)
    (z : Fin k → Bool) : ℕ := by
-- BODY
  classical
  exact Fintype.card
    {p : {v : Fin k → ProductDigraphVertex G //
        ForwardIndependentTuple (StarProductDigraph G) v} //
      StarProductMarkedTupleSignature G marked p.1 = z}
