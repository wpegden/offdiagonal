import Tablet.F2BadTuple

-- [TABLET NODE: F2BadTuplePrefixRestriction]

theorem F2BadTuplePrefixRestriction (p m : ℕ)
    (ab : Fin (m + 1) → (Fin p → ZMod 2) × (Fin p → ZMod 2)) :
    F2BadTuple p (m + 1) ab →
      F2BadTuple p m (fun i : Fin m => ab i.castSucc) := by
-- BODY
  intro hbad i j hji
  exact hbad i.castSucc j.castSucc hji
