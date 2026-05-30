import Tablet.BinarySequenceWeightFiberCard
import Tablet.F2BadTupleFixedIncreaseCount
import Tablet.F2BadTupleFixedIncreaseCountBound
import Tablet.F2BadTupleRankIncreaseSetCard

-- [TABLET NODE: F2BadTupleFinalRankFiberBound]

open Classical in
theorem F2BadTupleFinalRankFiberBound (p k t : ℕ) (hk : 0 < k)
    (ht : t ∈ Finset.Icc 1 p) :
    Fintype.card
        {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
          F2BadTuple p k ab ∧ F2BadTupleRank p k ab k = t} ≤
      Nat.choose k t * 2 ^ (p * (t + k) - Nat.choose (t + 1) 2) := by
-- BODY
  classical
  let A :=
    {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
      F2BadTuple p k ab ∧ F2BadTupleRank p k ab k = t}
  let Pattern := {z : Fin k → Bool // BinarySequenceWeight z = t}
  let Fiber : Pattern → Type :=
    fun z =>
      {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
        F2BadTuple p k ab ∧
          ∀ i : Fin k,
            (F2BadTupleRank p k ab (i.val + 1) =
                F2BadTupleRank p k ab i.val + 1) ↔ z.1 i = true}
  let C :=
    {za : (Fin k → Bool) × (Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) //
      BinarySequenceWeight za.1 = t ∧
        F2BadTuple p k za.2 ∧
          ∀ i : Fin k,
            (F2BadTupleRank p k za.2 (i.val + 1) =
                F2BadTupleRank p k za.2 i.val + 1) ↔ za.1 i = true}
  let pattern : A → Fin k → Bool :=
    fun ab i =>
      decide
        (F2BadTupleRank p k ab.1 (i.val + 1) =
          F2BadTupleRank p k ab.1 i.val + 1)
  have hpattern_weight : ∀ ab : A, BinarySequenceWeight (pattern ab) = t := by
    intro ab
    have hcard := (F2BadTupleRankIncreaseSetCard p k ab.1 ab.2.1 hk).2
    have hfilter :
        Finset.univ.filter (fun i : Fin k => pattern ab i = true) =
          F2BadTupleRankIncreaseSet p k ab.1 := by
      ext i
      simp [pattern, F2BadTupleRankIncreaseSet]
    rw [BinarySequenceWeight, hfilter, hcard, ab.2.2]
  let encode : A → C :=
    fun ab =>
      ⟨(pattern ab, ab.1), by
        constructor
        · exact hpattern_weight ab
        · constructor
          · exact ab.2.1
          · intro i
            simp [pattern]⟩
  have hencode_inj : Function.Injective encode := by
    intro ab ab' h
    apply Subtype.ext
    exact congrArg (fun x : C => x.1.2) h
  have hcard_le_C : Fintype.card A ≤ Fintype.card C :=
    Fintype.card_le_of_injective encode hencode_inj
  let cEquiv : C ≃ Sigma Fiber := {
    toFun := fun za =>
      ⟨⟨za.1.1, za.2.1⟩, ⟨za.1.2, za.2.2⟩⟩
    invFun := fun s =>
      ⟨(s.1.1, s.2.1), ⟨s.1.2, s.2.2⟩⟩
    left_inv := fun za => by
      cases za with
      | mk za hza =>
        rfl
    right_inv := fun s => by
      cases s with
      | mk z ab =>
        cases z with
        | mk z hz =>
          cases ab with
          | mk ab hab =>
            rfl
  }
  have ht_le_p : t ≤ p := (Finset.mem_Icc.mp ht).2
  let B := 2 ^ (p * (t + k) - Nat.choose (t + 1) 2)
  have hfiber_le : ∀ z : Pattern, Fintype.card (Fiber z) ≤ B := by
    intro z
    have hz_le : BinarySequenceWeight z.1 ≤ p := by
      rw [z.2]
      exact ht_le_p
    have hbound := F2BadTupleFixedIncreaseCountBound p k z.1 hz_le
    dsimp [B]
    simpa [Fiber, F2BadTupleFixedIncreaseCount, z.2] using hbound
  calc
    Fintype.card
        {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
          F2BadTuple p k ab ∧ F2BadTupleRank p k ab k = t}
        = Fintype.card A := rfl
    _ ≤ Fintype.card C := hcard_le_C
    _ = Fintype.card (Sigma Fiber) := Fintype.card_congr cEquiv
    _ = ∑ z : Pattern, Fintype.card (Fiber z) := Fintype.card_sigma
    _ ≤ ∑ z : Pattern, B := by
      exact Finset.sum_le_sum (fun z _ => hfiber_le z)
    _ = Nat.choose k t * B := by
      simp [Pattern, B, BinarySequenceWeightFiberCard]
