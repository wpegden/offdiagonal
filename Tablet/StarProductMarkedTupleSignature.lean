import Tablet.StarProductDigraph

-- [TABLET NODE: StarProductMarkedTupleSignature]

universe u

def StarProductMarkedTupleSignature {V : Type u}
    (G : LoopGraph V) {k : ℕ}
    (marked : ∀ m : ℕ, (Fin m → ProductDigraphVertex G) → ProductDigraphVertex G → Bool)
    (v : Fin k → ProductDigraphVertex G) : Fin k → Bool :=
-- BODY
  fun i =>
    ! marked i.1
      (fun j : Fin i.1 => v ⟨j.1, lt_trans j.2 i.2⟩)
      (v i)
