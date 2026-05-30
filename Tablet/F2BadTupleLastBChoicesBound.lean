import Tablet.F2BadTuplePrefixFiberBound

-- [TABLET NODE: F2BadTupleLastBChoicesBound]

theorem F2BadTupleLastBChoicesBound (p m t : ℕ)
    (pref : Fin m → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    (a : Fin p → ZMod 2) :
    Fintype.card
        {b : Fin p → ZMod 2 //
          F2BadTupleRank p (m + 1)
              (@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                pref (a, 0))
              (m + 1) = t ∧
            ∀ j : Fin (m + 1),
              ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                pref (a, 0)) j).1 ⬝ᵥ b = 1} ≤
      2 ^ (p - t) := by
-- BODY
  classical
  let ab0 : Fin (m + 1) → (Fin p → ZMod 2) × (Fin p → ZMod 2) :=
    @Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2)) pref (a, 0)
  let Source : Type :=
    {b : Fin p → ZMod 2 //
      F2BadTupleRank p (m + 1) ab0 (m + 1) = t ∧
        ∀ j : Fin (m + 1), (ab0 j).1 ⬝ᵥ b = 1}
  let Sol0 : Type :=
    {y : Fin p → ZMod 2 //
      ∀ j : {j : Fin (m + 1) // j.val < m + 1}, (ab0 j.1).1 ⬝ᵥ y = 1}
  change Fintype.card Source ≤ 2 ^ (p - t)
  by_cases hrank : F2BadTupleRank p (m + 1) ab0 (m + 1) = t
  · let f : Source → Sol0 := fun b =>
      ⟨b.val, by
        intro j
        exact b.property.2 j.1⟩
    have hinj : Function.Injective f := by
      intro b c hbc
      apply Subtype.ext
      exact congrArg (fun s : Sol0 => s.val) hbc
    refine (Fintype.card_le_of_injective f hinj).trans ?_
    have hfiber := F2BadTuplePrefixFiberBound p (m + 1) ab0 (m + 1)
    simpa [Sol0, ab0, hrank] using hfiber
  · haveI : IsEmpty Source := ⟨fun b => hrank b.property.1⟩
    simp [Source]
