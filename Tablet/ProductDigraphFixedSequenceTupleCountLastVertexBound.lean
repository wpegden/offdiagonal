import Tablet.ProductDigraphFixedSequenceTupleCount
import Tablet.ProductDigraphVertexCard

-- [TABLET NODE: ProductDigraphFixedSequenceTupleCountLastVertexBound]

universe u

theorem ProductDigraphFixedSequenceTupleCountLastVertexBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (n dF dG m : ℕ) (lambdaF : ℝ)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (w : Fin (m + 1) → Bool) :
    ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) w : ℕ) : ℝ) ≤
      ((ProductDigraphFixedSequenceTupleCount F G n dG m
        (fun i : Fin m => w i.castSucc) : ℕ) : ℝ) *
        (((dF * n : ℕ) : ℝ)) := by
-- BODY
  classical
  letI : Fintype (ProductDigraphVertex F) := Fintype.ofFinite _
  let Full :=
    {v : Fin (m + 1) → ProductDigraphVertex F //
      ProductDigraphTupleHasShrinkingSequence F G n dG v w}
  let Prefix :=
    {v : Fin m → ProductDigraphVertex F //
      ProductDigraphTupleHasShrinkingSequence F G n dG v
        (fun i : Fin m => w i.castSucc)}
  have hPrefix (v : Fin (m + 1) → ProductDigraphVertex F)
      (hv : ProductDigraphTupleHasShrinkingSequence F G n dG v w) :
      ProductDigraphTupleHasShrinkingSequence F G n dG
        (fun i : Fin m => v i.castSucc)
        (fun i : Fin m => w i.castSucc) := by
    unfold ProductDigraphTupleHasShrinkingSequence at hv ⊢
    rcases hv with ⟨hForward, hBits⟩
    constructor
    · intro i j hij
      exact hForward i.castSucc j.castSucc (by simpa using hij)
    · intro i
      specialize hBits i.castSucc
      have hB :
          (Finset.univ.filter
            (fun b : V => ∀ j : Fin m, j < i → ¬ G (v j.castSucc).val.1 b)) =
          (Finset.univ.filter
            (fun b : V => ∀ j : Fin (m + 1), j < i.castSucc → ¬ G (v j).val.1 b)) := by
        ext b
        constructor
        · intro hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          intro j hj
          obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
          have hklt : k.castSucc < i.castSucc := by simpa [hk] using hj
          rw [← hk]
          exact hb k (by simpa using hklt)
        · intro hb
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
          intro j hj
          exact hb j.castSucc (by simpa using hj)
      simpa [hB] using hBits
  let encode : Full → Prefix × ProductDigraphVertex F := fun v =>
    (⟨fun i : Fin m => v.val i.castSucc, hPrefix v.val v.property⟩,
      v.val (Fin.last m))
  have hencode_inj : Function.Injective encode := by
    intro x y hxy
    dsimp [encode] at hxy
    have hprefixSubtype := congrArg Prod.fst hxy
    have hlast := congrArg Prod.snd hxy
    have hprefix :
        (fun i : Fin m => x.val i.castSucc) =
          (fun i : Fin m => y.val i.castSucc) := by
      exact congrArg Subtype.val hprefixSubtype
    apply Subtype.ext
    funext i
    exact Fin.lastCases hlast (fun j => congr_fun hprefix j) i
  have hcard_nat :
      Fintype.card Full ≤ Fintype.card (Prefix × ProductDigraphVertex F) :=
    Fintype.card_le_of_injective encode hencode_inj
  have hcard_real :
      ((Fintype.card Full : ℕ) : ℝ) ≤
        ((Fintype.card (Prefix × ProductDigraphVertex F) : ℕ) : ℝ) := by
    exact_mod_cast hcard_nat
  have hvertex :
      Fintype.card (ProductDigraphVertex F) = dF * n :=
    ProductDigraphVertexCard F n dF lambdaF hF
  simpa [ProductDigraphFixedSequenceTupleCount, Full, Prefix, Fintype.card_prod,
    hvertex, Nat.cast_mul, mul_assoc] using hcard_real

