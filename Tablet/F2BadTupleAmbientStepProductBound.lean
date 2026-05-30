import Tablet.F2BadTuplePrefixFiberBound

-- [TABLET NODE: F2BadTupleAmbientStepProductBound]

theorem F2BadTupleAmbientStepProductBound (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) (i : ℕ) :
    Fintype.card (Fin p → ZMod 2) *
        Fintype.card
          {y : Fin p → ZMod 2 //
            ∀ j : {j : Fin k // j.val < i}, (ab j.1).1 ⬝ᵥ y = 1} ≤
      2 ^ p * 2 ^ (p - F2BadTupleRank p k ab i) := by
-- BODY
  classical
  have hvec : Fintype.card (Fin p → ZMod 2) = 2 ^ p := by
    rw [Fintype.card_fun]
    norm_num [ZMod.card]
  have hfiber := F2BadTuplePrefixFiberBound p k ab i
  rw [hvec]
  exact Nat.mul_le_mul_left _ hfiber
