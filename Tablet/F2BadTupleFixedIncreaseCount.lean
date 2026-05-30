import Tablet.BinarySequenceWeight
import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleFixedIncreaseCount]

noncomputable def F2BadTupleFixedIncreaseCount (p k : ℕ) (z : Fin k → Bool) : ℕ := by
-- BODY
  classical
  exact
    Fintype.card
      {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
        F2BadTuple p k ab ∧
          ∀ i : Fin k,
            (F2BadTupleRank p k ab (i.val + 1) =
                F2BadTupleRank p k ab i.val + 1) ↔ z i = true}
