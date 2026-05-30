import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleRankStep]

theorem F2BadTupleRankStep (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    {i : ℕ} (hi : i < k) :
    F2BadTupleRank p k ab (i + 1) = F2BadTupleRank p k ab i ∨
      F2BadTupleRank p k ab (i + 1) = F2BadTupleRank p k ab i + 1 := by
-- BODY
  classical
  let prev : Submodule (ZMod 2) (Fin p → ZMod 2) :=
    Submodule.span (ZMod 2)
      (Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1))
  let v : Fin p → ZMod 2 := (ab ⟨i, hi⟩).1
  have hrange :
      Set.range (fun j : {j : Fin k // j.val < i + 1} => (ab j.1).1) =
        Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1) ∪ {v} := by
    ext w
    constructor
    · rintro ⟨j, rfl⟩
      by_cases hlt : j.1.val < i
      · left
        exact ⟨⟨j.1, hlt⟩, rfl⟩
      · right
        have hEq : j.1.val = i := by omega
        have hj : j.1 = ⟨i, hi⟩ := by
          apply Fin.ext
          simpa using hEq
        simp [v, hj]
    · intro hw
      rcases hw with hw | hw
      · rcases hw with ⟨j, rfl⟩
        exact ⟨⟨j.1, by omega⟩, rfl⟩
      · have hw' : w = v := by simpa using hw
        subst w
        exact ⟨⟨⟨i, hi⟩, by simp⟩, rfl⟩
  have hspan :
      Submodule.span (ZMod 2)
          (Set.range (fun j : {j : Fin k // j.val < i + 1} => (ab j.1).1)) =
        prev ⊔ (ZMod 2) ∙ v := by
    rw [hrange, Submodule.span_union]
  by_cases hv : v ∈ prev
  · left
    dsimp [F2BadTupleRank]
    have hsup : prev ⊔ (ZMod 2) ∙ v = prev := by
      exact sup_eq_left.mpr ((Submodule.span_singleton_le_iff_mem v prev).mpr hv)
    rw [hspan, hsup]
  · right
    dsimp [F2BadTupleRank]
    rw [hspan]
    exact Submodule.finrank_sup_span_singleton hv
