import Tablet.F2BadTuple

-- [TABLET NODE: F2BadTupleRank]

noncomputable def F2BadTupleRank (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) (i : ℕ) : ℕ :=
-- BODY
  Module.finrank (ZMod 2)
    (Submodule.span (ZMod 2)
      (Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1)))
