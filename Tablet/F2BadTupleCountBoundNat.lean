import Tablet.F2BadTupleFinalRankFiberBound
import Tablet.F2BadTupleRankIncreaseSetCard

-- [TABLET NODE: F2BadTupleCountBoundNat]

open Classical in
theorem F2BadTupleCountBoundNat (p k : ℕ) (hk : 0 < k) :
    Fintype.card
        {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
          F2BadTuple p k ab} ≤
      Finset.sum (Finset.Icc 1 p)
        (fun t => Nat.choose k t * 2 ^ (p * (t + k) - Nat.choose (t + 1) 2)) := by
-- BODY
  classical
  let Bad :=
    {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
      F2BadTuple p k ab}
  let RankFiber : {t : ℕ // t ∈ Finset.Icc 1 p} → Type :=
    fun t =>
      {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
        F2BadTuple p k ab ∧ F2BadTupleRank p k ab k = t.1}
  let C :=
    {ta : {t : ℕ // t ∈ Finset.Icc 1 p} ×
        (Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) //
      F2BadTuple p k ta.2 ∧ F2BadTupleRank p k ta.2 k = ta.1.1}
  letI : Fintype C := Fintype.ofFinite C
  let encode : Bad → C :=
    fun ab =>
      ⟨(⟨F2BadTupleRank p k ab.1 k,
          (F2BadTupleRankIncreaseSetCard p k ab.1 ab.2 hk).1⟩, ab.1), by
        constructor
        · exact ab.2
        · rfl⟩
  have hencode_inj : Function.Injective encode := by
    intro ab ab' h
    apply Subtype.ext
    exact congrArg (fun x : C => x.1.2) h
  have hcard_le_C : Fintype.card Bad ≤ Fintype.card C :=
    Fintype.card_le_of_injective encode hencode_inj
  let cEquiv : C ≃ Sigma RankFiber := {
    toFun := fun ta =>
      ⟨ta.1.1, ⟨ta.1.2, ta.2⟩⟩
    invFun := fun s =>
      ⟨(s.1, s.2.1), s.2.2⟩
    left_inv := fun ta => by
      cases ta with
      | mk ta hta =>
        rfl
    right_inv := fun s => by
      cases s with
      | mk t ab =>
        cases t with
        | mk t ht =>
          cases ab with
          | mk ab hab =>
            rfl
  }
  let B : ℕ → ℕ :=
    fun t => Nat.choose k t * 2 ^ (p * (t + k) - Nat.choose (t + 1) 2)
  have hfiber_le : ∀ t : {t : ℕ // t ∈ Finset.Icc 1 p},
      Fintype.card (RankFiber t) ≤ B t.1 := by
    intro t
    dsimp [RankFiber, B]
    exact F2BadTupleFinalRankFiberBound p k t.1 hk t.2
  calc
    Fintype.card
        {ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2) //
          F2BadTuple p k ab}
        = Fintype.card Bad := rfl
    _ ≤ Fintype.card C := hcard_le_C
    _ = Fintype.card (Sigma RankFiber) := Fintype.card_congr cEquiv
    _ = ∑ t : {t : ℕ // t ∈ Finset.Icc 1 p}, Fintype.card (RankFiber t) :=
        Fintype.card_sigma
    _ ≤ ∑ t : {t : ℕ // t ∈ Finset.Icc 1 p}, B t.1 := by
      exact Finset.sum_le_sum (fun t _ => hfiber_le t)
    _ = Finset.sum (Finset.Icc 1 p) B := by
      simpa using (Finset.sum_attach (s := Finset.Icc 1 p) (f := B))
