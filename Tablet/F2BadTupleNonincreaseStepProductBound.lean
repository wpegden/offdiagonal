import Tablet.F2BadTuplePrefixFiberBound
import Tablet.F2BadTuplePrefixSpanCard
import Tablet.F2BadTupleRankStep

-- [TABLET NODE: F2BadTupleNonincreaseStepProductBound]

theorem F2BadTupleNonincreaseStepProductBound (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    {i : ℕ} (hi : i < k)
    (hsame : F2BadTupleRank p k ab (i + 1) = F2BadTupleRank p k ab i) :
    (ab ⟨i, hi⟩).1 ∈
        Submodule.span (ZMod 2)
          (Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1)) ∧
      Nat.card
          (Submodule.span (ZMod 2)
            (Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1))) *
          Fintype.card
            {y : Fin p → ZMod 2 //
              ∀ j : {j : Fin k // j.val < i + 1}, (ab j.1).1 ⬝ᵥ y = 1} ≤
        2 ^ F2BadTupleRank p k ab i *
          2 ^ (p - F2BadTupleRank p k ab i) := by
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
  have hmem : v ∈ prev := by
    by_contra hv
    have hrank_succ :
        F2BadTupleRank p k ab (i + 1) = F2BadTupleRank p k ab i + 1 := by
      dsimp [F2BadTupleRank]
      rw [hspan]
      exact Submodule.finrank_sup_span_singleton hv
    omega
  have hspan_card := F2BadTuplePrefixSpanCard p k ab i
  have hfiber := F2BadTuplePrefixFiberBound p k ab (i + 1)
  have hfiber' :
      Fintype.card
          {y : Fin p → ZMod 2 //
            ∀ j : {j : Fin k // j.val < i + 1}, (ab j.1).1 ⬝ᵥ y = 1} ≤
        2 ^ (p - F2BadTupleRank p k ab i) := by
    simpa [hsame] using hfiber
  constructor
  · exact hmem
  · rw [hspan_card]
    exact Nat.mul_le_mul_left _ hfiber'
