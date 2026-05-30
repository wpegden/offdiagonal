import Tablet.F2BadTupleLastBChoicesBound

-- [TABLET NODE: F2BadTupleLastPairAmbientFiberBound]

theorem F2BadTupleLastPairAmbientFiberBound (p m t : ℕ)
    (pref : Fin m → (Fin p → ZMod 2) × (Fin p → ZMod 2)) :
    Fintype.card
        {pair : (Fin p → ZMod 2) × (Fin p → ZMod 2) //
          F2BadTupleRank p (m + 1)
              (@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                pref (pair.1, 0))
              (m + 1) = t ∧
            ∀ j : Fin (m + 1),
              ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                pref (pair.1, 0)) j).1 ⬝ᵥ pair.2 = 1} ≤
      2 ^ p * 2 ^ (p - t) := by
-- BODY
  classical
  let Vec : Type := Fin p → ZMod 2
  let B : Vec → Type := fun a =>
    {b : Vec //
      F2BadTupleRank p (m + 1)
          (@Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)) (m + 1) = t ∧
        ∀ j : Fin (m + 1),
          ((@Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)) j).1 ⬝ᵥ b = 1}
  let Source : Type :=
    {pair : Vec × Vec //
      F2BadTupleRank p (m + 1)
          (@Fin.snoc m (fun _ => Vec × Vec) pref (pair.1, 0)) (m + 1) = t ∧
        ∀ j : Fin (m + 1),
          ((@Fin.snoc m (fun _ => Vec × Vec) pref (pair.1, 0)) j).1 ⬝ᵥ pair.2 = 1}
  change Fintype.card Source ≤ 2 ^ p * 2 ^ (p - t)
  have hinj :
      Function.Injective
        (fun x : Source => (⟨x.val.1, ⟨x.val.2, x.property⟩⟩ : Sigma B)) := by
    intro x y hxy
    apply Subtype.ext
    have h1 : x.val.1 = y.val.1 := by
      exact congrArg Sigma.fst hxy
    have h2 : x.val.2 = y.val.2 := by
      exact congrArg (fun s : Sigma B => (s.2 : Vec)) hxy
    exact Prod.ext h1 h2
  have hle_sigma : Fintype.card Source ≤ Fintype.card (Sigma B) :=
    Fintype.card_le_of_injective _ hinj
  have hcard_sigma :
      Fintype.card (Sigma B) = Finset.univ.sum (fun a : Vec => Fintype.card (B a)) := by
    simp [B]
  have hsum_le :
      Finset.univ.sum (fun a : Vec => Fintype.card (B a)) ≤
        Finset.univ.sum (fun _ : Vec => 2 ^ (p - t)) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    simpa [B, Vec] using F2BadTupleLastBChoicesBound p m t pref a
  have hsum_const :
      Finset.univ.sum (fun _ : Vec => 2 ^ (p - t)) =
        Fintype.card Vec * 2 ^ (p - t) := by
    simp
  have hvec : Fintype.card Vec = 2 ^ p := by
    rw [Fintype.card_fun]
    norm_num [ZMod.card, Vec]
  calc
    Fintype.card Source ≤ Fintype.card (Sigma B) := hle_sigma
    _ = Finset.univ.sum (fun a : Vec => Fintype.card (B a)) := hcard_sigma
    _ ≤ Finset.univ.sum (fun _ : Vec => 2 ^ (p - t)) := hsum_le
    _ = Fintype.card Vec * 2 ^ (p - t) := hsum_const
    _ = 2 ^ p * 2 ^ (p - t) := by rw [hvec]
