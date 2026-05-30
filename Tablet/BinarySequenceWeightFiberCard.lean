import Tablet.BinarySequenceWeight

-- [TABLET NODE: BinarySequenceWeightFiberCard]

theorem BinarySequenceWeightFiberCard (k t : ℕ) :
    Fintype.card {z : Fin k → Bool // BinarySequenceWeight z = t} = Nat.choose k t := by
-- BODY
  classical
  let toFinset (z : Fin k → Bool) : Finset (Fin k) :=
    Finset.univ.filter (fun i : Fin k => z i = true)
  let fromFinset (S : Finset (Fin k)) : Fin k → Bool :=
    fun i => decide (i ∈ S)
  let e :
      {z : Fin k → Bool // BinarySequenceWeight z = t} ≃
        {S : Finset (Fin k) // S.card = t} := {
    toFun := fun z => ⟨toFinset z.1, by
      simpa [BinarySequenceWeight, toFinset] using z.2⟩
    invFun := fun S => ⟨fromFinset S.1, by
      rw [BinarySequenceWeight]
      have hfilter : Finset.univ.filter (fun i : Fin k => fromFinset S.1 i = true) = S.1 := by
        ext i
        simp [fromFinset]
      rw [hfilter]
      exact S.2⟩
    left_inv := fun z => by
      ext i
      simp [fromFinset, toFinset]
    right_inv := fun S => by
      ext i
      simp [fromFinset, toFinset]
  }
  let epowerset :
      {S : Finset (Fin k) // S.card = t} ≃
        {S : Finset (Fin k) // S ∈ (Finset.univ : Finset (Fin k)).powersetCard t} :=
    Equiv.subtypeEquivRight (fun S => by
      simp [Finset.mem_powersetCard])
  calc
    Fintype.card {z : Fin k → Bool // BinarySequenceWeight z = t}
        = Fintype.card {S : Finset (Fin k) // S.card = t} := Fintype.card_congr e
    _ = Fintype.card {S : Finset (Fin k) //
        S ∈ (Finset.univ : Finset (Fin k)).powersetCard t} := Fintype.card_congr epowerset
    _ = ((Finset.univ : Finset (Fin k)).powersetCard t).card :=
        Fintype.card_of_subtype ((Finset.univ : Finset (Fin k)).powersetCard t)
          (fun S => Iff.rfl)
    _ = Nat.choose k t := by
      simp [Finset.card_powersetCard]
