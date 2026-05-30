import Tablet.F2BadTupleFixedIncreaseCount
import Tablet.F2BadTuplePrefixRestriction
import Tablet.F2BadTupleRankPrefixRestriction

-- [TABLET NODE: F2BadTupleFixedIncreasePrefixRestriction]

theorem F2BadTupleFixedIncreasePrefixRestriction (p m : ℕ)
    (ab : Fin (m + 1) → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    (z : Fin (m + 1) → Bool) :
    (F2BadTuple p (m + 1) ab ∧
        ∀ i : Fin (m + 1),
          (F2BadTupleRank p (m + 1) ab (i.val + 1) =
              F2BadTupleRank p (m + 1) ab i.val + 1) ↔ z i = true) →
      F2BadTuple p m (fun i : Fin m => ab i.castSucc) ∧
        ∀ i : Fin m,
          (F2BadTupleRank p m (fun j : Fin m => ab j.castSucc) (i.val + 1) =
              F2BadTupleRank p m (fun j : Fin m => ab j.castSucc) i.val + 1) ↔
            z i.castSucc = true := by
-- BODY
  rintro ⟨hbad, hpattern⟩
  constructor
  · exact F2BadTuplePrefixRestriction p m ab hbad
  · intro i
    have h1 :
        F2BadTupleRank p (m + 1) ab (i.val + 1) =
          F2BadTupleRank p m (fun j : Fin m => ab j.castSucc) (i.val + 1) := by
      exact F2BadTupleRankPrefixRestriction p m ab (i.val + 1) (Nat.succ_le_of_lt i.2)
    have h0 :
        F2BadTupleRank p (m + 1) ab i.val =
          F2BadTupleRank p m (fun j : Fin m => ab j.castSucc) i.val := by
      exact F2BadTupleRankPrefixRestriction p m ab i.val (Nat.le_of_lt i.2)
    rw [← h1, ← h0]
    exact hpattern i.castSucc
