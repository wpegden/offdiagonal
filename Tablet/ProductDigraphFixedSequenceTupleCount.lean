import Tablet.ProductDigraphTupleHasShrinkingSequence

-- [TABLET NODE: ProductDigraphFixedSequenceTupleCount]

universe u

noncomputable def ProductDigraphFixedSequenceTupleCount {V : Type u} [Fintype V]
    (F G : LoopGraph V) (n dG t : ℕ) (z : Fin t → Bool) : ℕ := by
-- BODY
  classical
  letI : Fintype (ProductDigraphVertex F) := Fintype.ofFinite _
  letI : DecidablePred
      (fun v : Fin t → ProductDigraphVertex F =>
        ProductDigraphTupleHasShrinkingSequence F G n dG v z) :=
    Classical.decPred _
  exact Fintype.card
    {v : Fin t → ProductDigraphVertex F //
      ProductDigraphTupleHasShrinkingSequence F G n dG v z}
