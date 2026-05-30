import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleRankPrefixRestriction]

theorem F2BadTupleRankPrefixRestriction (p m : ℕ)
    (ab : Fin (m + 1) → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    (i : ℕ) (hi : i ≤ m) :
    F2BadTupleRank p (m + 1) ab i =
      F2BadTupleRank p m (fun j : Fin m => ab j.castSucc) i := by
-- BODY
  unfold F2BadTupleRank
  have hset :
      Set.range (fun j : {j : Fin (m + 1) // j.val < i} => (ab j.1).1) =
        Set.range
          (fun j : {j : Fin m // j.val < i} =>
            ((fun j : Fin m => ab j.castSucc) j.1).1) := by
    ext v
    constructor
    · intro hv
      rcases hv with ⟨j, rfl⟩
      have hj_lt_m : j.1.val < m := lt_of_lt_of_le j.2 hi
      refine ⟨⟨⟨j.1.val, hj_lt_m⟩, j.2⟩, ?_⟩
      rfl
    · intro hv
      rcases hv with ⟨j, rfl⟩
      refine ⟨⟨j.1.castSucc, j.2⟩, ?_⟩
      rfl
  rw [hset]
