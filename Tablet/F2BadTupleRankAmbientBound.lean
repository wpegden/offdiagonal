import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleRankAmbientBound]

theorem F2BadTupleRankAmbientBound (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) (i : ℕ) :
    F2BadTupleRank p k ab i ≤ p := by
-- BODY
  dsimp [F2BadTupleRank]
  calc
    Module.finrank (ZMod 2)
        (Submodule.span (ZMod 2)
          (Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1)))
        ≤ Module.finrank (ZMod 2) (Fin p → ZMod 2) :=
          Submodule.finrank_le _
    _ = p := by
          rw [Module.finrank_fin_fun]
