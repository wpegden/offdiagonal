import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleRankZero]

theorem F2BadTupleRankZero (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) :
    F2BadTupleRank p k ab 0 = 0 := by
-- BODY
  simp [F2BadTupleRank]
