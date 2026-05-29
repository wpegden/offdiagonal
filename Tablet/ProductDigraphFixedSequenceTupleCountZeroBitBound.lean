import Tablet.ProductDigraphFixedSequenceTupleCount
import Tablet.ProductDigraphSparseEdgeChoiceBound

-- [TABLET NODE: ProductDigraphFixedSequenceTupleCountZeroBitBound]

universe u

theorem ProductDigraphFixedSequenceTupleCountZeroBitBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (n dF dG m : ℕ) (lambdaF lambdaG eta : ℝ)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hn : 0 < n) (hdF : 0 < dF) (hdG : 0 < dG)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (w : Fin (m + 1) → Bool)
    (hw : w (Fin.last m) = false) :
    ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) w : ℕ) : ℝ) ≤
      ((ProductDigraphFixedSequenceTupleCount F G n dG m
        (fun i : Fin m => w i.castSucc) : ℕ) : ℝ) *
        (((8 : ℝ) * eta) * (((dF * n : ℕ) : ℝ))) := by
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
  let B (p : Prefix) : Finset V :=
    Finset.univ.filter (fun b : V => ∀ j : Fin m, ¬ G (p.val j).val.1 b)
  let A (p : Prefix) : Finset V :=
    Finset.univ.filter (fun u : V =>
      ((LoopGraphEdgeCountBetween G ({u} : Finset V) (B p) : ℕ) : ℝ) ≤
        ((dG : ℝ) * ((B p).card : ℝ)) / (2 * (n : ℝ)))
  let EdgeOption (p : Prefix) :=
    {q : V × V // q ∈ ((A p).product (B p)).filter (fun q : V × V => F q.1 q.2)}
  let Target :=
    {r : Prefix × (V × V) //
      r.2 ∈ ((A r.1).product (B r.1)).filter (fun q : V × V => F q.1 q.2)}
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
  have hB_last (v : Fin (m + 1) → ProductDigraphVertex F)
      (p : Prefix)
      (hp : p.val = fun i : Fin m => v i.castSucc) :
      (Finset.univ.filter
        (fun b : V => ∀ j : Fin (m + 1), j < Fin.last m → ¬ G (v j).val.1 b)) =
        B p := by
    ext b
    constructor
    · intro hb
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      intro j
      have hj : j.castSucc < Fin.last m := Fin.castSucc_lt_last j
      have := hb j.castSucc hj
      simpa [hp] using this
    · intro hb
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      intro j hj
      obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last (Fin.ne_last_of_lt hj)
      rw [← hk]
      have := hb k
      simpa [hp] using this
  let encode : Full → Target := fun v =>
    let p : Prefix := ⟨fun i : Fin m => v.val i.castSucc, hPrefix v.val v.property⟩
    have hpval : p.val = fun i : Fin m => v.val i.castSucc := rfl
    have hForward :
        ForwardIndependentTuple (ProductDigraph F G) v.val := by
      have hvprop := v.property
      unfold ProductDigraphTupleHasShrinkingSequence at hvprop
      exact hvprop.1
    have hBmem : (v.val (Fin.last m)).val.2 ∈ B p := by
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      intro j
      have hno := hForward j.castSucc (Fin.last m) (Fin.castSucc_lt_last j)
      simpa [ProductDigraph] using hno
    have hAmem : (v.val (Fin.last m)).val.1 ∈ A p := by
      have hvprop := v.property
      unfold ProductDigraphTupleHasShrinkingSequence at hvprop
      rcases hvprop with ⟨_hForward, hBits⟩
      have hLastBits := hBits (Fin.last m)
      let Bfull : Finset V :=
        Finset.univ.filter
          (fun b : V => ∀ j : Fin (m + 1), j < Fin.last m → ¬ G (v.val j).val.1 b)
      have hnot :
          ¬ ((dG : ℝ) * ((Bfull.card : ℝ))) / (2 * (n : ℝ)) <
            ((LoopGraphEdgeCountBetween G ({(v.val (Fin.last m)).val.1} : Finset V)
              Bfull : ℕ) : ℝ) := by
        intro hlt
        have htrue : w (Fin.last m) = true := hLastBits.mpr hlt
        simp [hw] at htrue
      have hle :
          ((LoopGraphEdgeCountBetween G ({(v.val (Fin.last m)).val.1} : Finset V)
              Bfull : ℕ) : ℝ) ≤
            ((dG : ℝ) * ((Bfull.card : ℝ))) / (2 * (n : ℝ)) :=
        le_of_not_gt hnot
      have hBfull_eq : Bfull = B p := by
        simpa [Bfull] using hB_last v.val p hpval
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and]
      simpa [hBfull_eq] using hle
    ⟨(p, (v.val (Fin.last m)).val), by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨hAmem, hBmem⟩,
        (v.val (Fin.last m)).property⟩
    ⟩
  have hencode_inj : Function.Injective encode := by
    intro x y hxy
    dsimp [encode] at hxy
    have hval := congrArg Subtype.val hxy
    have hprefix :
        (fun i : Fin m => x.val i.castSucc) =
          (fun i : Fin m => y.val i.castSucc) := by
      exact congrArg Subtype.val (congrArg Prod.fst hval)
    have hlastPair : (x.val (Fin.last m)).val = (y.val (Fin.last m)).val := by
      exact congrArg Prod.snd hval
    apply Subtype.ext
    funext i
    exact Fin.lastCases (Subtype.ext hlastPair) (fun j => congr_fun hprefix j) i
  have hcard_nat :
      Fintype.card Full ≤ Fintype.card Target :=
    Fintype.card_le_of_injective encode hencode_inj
  let targetEquiv : Target ≃ Sigma EdgeOption :=
    { toFun := fun r => ⟨r.val.1, ⟨r.val.2, r.property⟩⟩
      invFun := fun s => ⟨(s.1, s.2.val), s.2.property⟩
      left_inv := by
        intro r
        cases r with
        | mk val h =>
          cases val
          rfl
      right_inv := by
        intro s
        cases s with
        | mk p q =>
          cases q
          rfl }
  let K : ℝ := ((8 : ℝ) * eta) * (((dF * n : ℕ) : ℝ))
  have hEdgeEach :
      ∀ p : Prefix, ((Fintype.card (EdgeOption p) : ℕ) : ℝ) ≤ K := by
    intro p
    have hcard_eq :
        Fintype.card (EdgeOption p) = LoopGraphEdgeCountBetween F (A p) (B p) := by
      rw [Fintype.card_subtype]
      change
        (Finset.univ.filter
          (fun q : V × V =>
            q ∈ ((A p).product (B p)).filter (fun q : V × V => F q.1 q.2))).card =
          (((A p).product (B p)).filter (fun q : V × V => F q.1 q.2)).card
      have hfin :
          Finset.univ.filter
            (fun q : V × V =>
              q ∈ ((A p).product (B p)).filter (fun q : V × V => F q.1 q.2)) =
            ((A p).product (B p)).filter (fun q : V × V => F q.1 q.2) := by
        ext q
        simp
      rw [hfin]
    have hSparse :
        ((LoopGraphEdgeCountBetween F (A p) (B p) : ℕ) : ℝ) ≤ K := by
      dsimp [K]
      exact ProductDigraphSparseEdgeChoiceBound F G n dF dG lambdaF lambdaG eta
        hF hG hn hdF hdG heta (A p) (B p) (by
          intro u
          simp [A])
    simpa [hcard_eq] using hSparse
  have hsigma_real :
      ((Fintype.card (Sigma EdgeOption) : ℕ) : ℝ) ≤
        ((Fintype.card Prefix : ℕ) : ℝ) * K := by
    calc
      ((Fintype.card (Sigma EdgeOption) : ℕ) : ℝ)
          = ∑ p : Prefix, ((Fintype.card (EdgeOption p) : ℕ) : ℝ) := by
            simp [Fintype.card_sigma]
      _ ≤ ∑ _p : Prefix, K := by
            exact Finset.sum_le_sum (fun p _hp => hEdgeEach p)
      _ = ((Fintype.card Prefix : ℕ) : ℝ) * K := by
            simp [mul_comm]
  have hcard_real :
      ((Fintype.card Full : ℕ) : ℝ) ≤
        ((Fintype.card Prefix : ℕ) : ℝ) * K := by
    have htarget_card :
        Fintype.card Target = Fintype.card (Sigma EdgeOption) :=
      Fintype.card_congr targetEquiv
    have htarget_real :
        ((Fintype.card Target : ℕ) : ℝ) ≤
          ((Fintype.card Prefix : ℕ) : ℝ) * K := by
      simpa [htarget_card] using hsigma_real
    exact le_trans (by exact_mod_cast hcard_nat) htarget_real
  simpa [ProductDigraphFixedSequenceTupleCount, Full, Prefix, K, mul_assoc] using hcard_real

