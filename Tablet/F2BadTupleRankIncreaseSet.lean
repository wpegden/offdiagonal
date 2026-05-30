import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleRankIncreaseSet]

noncomputable def F2BadTupleRankIncreaseSet (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) : Finset (Fin k) :=
-- BODY
  Finset.univ.filter
    (fun i : Fin k =>
      F2BadTupleRank p k ab (i.val + 1) = F2BadTupleRank p k ab i.val + 1)
