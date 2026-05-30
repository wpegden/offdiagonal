import Tablet.F2BadTupleLastBChoicesBound
import Tablet.F2BadTupleNonincreaseStepProductBound
import Tablet.F2BadTuplePrefixSpanCard
import Tablet.F2BadTupleRankPrefixRestriction

-- [TABLET NODE: F2BadTupleLastPairSpanFiberBound]

theorem F2BadTupleLastPairSpanFiberBound (p m t : ℕ)
    (pref : Fin m → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    (hrank_pref : F2BadTupleRank p m pref m = t) :
    Fintype.card
        {pair : (Fin p → ZMod 2) × (Fin p → ZMod 2) //
          F2BadTupleRank p (m + 1)
              (@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                pref (pair.1, 0))
              (m + 1) = t ∧
            ∀ j : Fin (m + 1),
              ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                pref (pair.1, 0)) j).1 ⬝ᵥ pair.2 = 1} ≤
      2 ^ t * 2 ^ (p - t) := by
-- BODY
  classical
  let Vec : Type := Fin p → ZMod 2
  let Span : Submodule (ZMod 2) Vec :=
    Submodule.span (ZMod 2)
      (Set.range (fun j : {j : Fin m // j.val < m} => (pref j.1).1))
  haveI : Fintype Span := Fintype.ofFinite Span
  let Source : Type :=
    {pair : Vec × Vec //
      F2BadTupleRank p (m + 1)
          (@Fin.snoc m (fun _ => Vec × Vec) pref (pair.1, 0))
          (m + 1) = t ∧
        ∀ j : Fin (m + 1),
          ((@Fin.snoc m (fun _ => Vec × Vec) pref (pair.1, 0)) j).1 ⬝ᵥ
            pair.2 = 1}
  let B : Span → Type := fun a =>
    {b : Vec //
      F2BadTupleRank p (m + 1)
          (@Fin.snoc m (fun _ => Vec × Vec) pref (a.val, 0))
          (m + 1) = t ∧
        ∀ j : Fin (m + 1),
          ((@Fin.snoc m (fun _ => Vec × Vec) pref (a.val, 0)) j).1 ⬝ᵥ b = 1}
  change Fintype.card Source ≤ 2 ^ t * 2 ^ (p - t)
  have hspan_card : Fintype.card Span = 2 ^ t := by
    rw [← Nat.card_eq_fintype_card]
    simpa [Span, Vec, hrank_pref] using F2BadTuplePrefixSpanCard p m pref m
  have hprefix_rank :
      ∀ a : Vec,
        F2BadTupleRank p (m + 1)
            (@Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)) m = t := by
    intro a
    let ab0 : Fin (m + 1) → Vec × Vec :=
      @Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)
    calc
      F2BadTupleRank p (m + 1) ab0 m =
          F2BadTupleRank p m (fun j : Fin m => ab0 j.castSucc) m := by
          exact F2BadTupleRankPrefixRestriction p m ab0 m (le_refl m)
      _ = F2BadTupleRank p m pref m := by
          simp [ab0]
      _ = t := hrank_pref
  have hfull_prefix_span :
      ∀ a : Vec,
        Submodule.span (ZMod 2)
            (Set.range
              (fun j : {j : Fin (m + 1) // j.val < m} =>
                ((@Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)) j.1).1)) =
          Span := by
    intro a
    apply congrArg (Submodule.span (ZMod 2))
    ext v
    constructor
    · intro hv
      rcases hv with ⟨j, rfl⟩
      have hlt : j.1.val < m := j.2
      let jj : Fin m := ⟨j.1.val, hlt⟩
      refine ⟨⟨jj, jj.isLt⟩, ?_⟩
      have hjj : jj.castSucc = j.1 := by
        apply Fin.ext
        rfl
      change
        (pref jj).1 =
          ((@Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)) j.1).1
      calc
        (pref jj).1 =
            ((@Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)) jj.castSucc).1 := by
            simp
        _ = ((@Fin.snoc m (fun _ => Vec × Vec) pref (a, 0)) j.1).1 := by
            rw [hjj]
    · intro hv
      rcases hv with ⟨j, rfl⟩
      refine ⟨⟨j.1.castSucc, by simpa only [Fin.val_castSucc] using j.2⟩, ?_⟩
      simp
  have hmem_span : ∀ pair : Source, pair.val.1 ∈ Span := by
    intro pair
    let ab0 : Fin (m + 1) → Vec × Vec :=
      @Fin.snoc m (fun _ => Vec × Vec) pref (pair.val.1, 0)
    have hsame :
        F2BadTupleRank p (m + 1) ab0 (m + 1) =
          F2BadTupleRank p (m + 1) ab0 m := by
      rw [pair.property.1, hprefix_rank pair.val.1]
    have hmem_full :
        (ab0 ⟨m, Nat.lt_succ_self m⟩).1 ∈
          Submodule.span (ZMod 2)
            (Set.range
              (fun j : {j : Fin (m + 1) // j.val < m} => (ab0 j.1).1)) :=
      (F2BadTupleNonincreaseStepProductBound p (m + 1) ab0
        (i := m) (Nat.lt_succ_self m) hsame).1
    have hlast : (ab0 ⟨m, Nat.lt_succ_self m⟩).1 = pair.val.1 := by
      have hidx : (⟨m, Nat.lt_succ_self m⟩ : Fin (m + 1)) = Fin.last m := by
        apply Fin.ext
        simp
      rw [hidx]
      simp [ab0]
    simpa [ab0, hlast, hfull_prefix_span pair.val.1] using hmem_full
  let toSigma : Source → Sigma B := fun pair =>
    let a : Span := ⟨pair.val.1, hmem_span pair⟩
    ⟨a, ⟨pair.val.2, by
      simpa [B, a] using pair.property⟩⟩
  have hinj : Function.Injective toSigma := by
    intro pair₁ pair₂ h
    apply Subtype.ext
    have ha : pair₁.val.1 = pair₂.val.1 := by
      exact congrArg Subtype.val (congrArg Sigma.fst h)
    have hb : pair₁.val.2 = pair₂.val.2 := by
      exact congrArg (fun s : Sigma B => (s.2 : Vec)) h
    exact Prod.ext ha hb
  have hle_sigma : Fintype.card Source ≤ Fintype.card (Sigma B) :=
    Fintype.card_le_of_injective toSigma hinj
  have hcard_sigma :
      Fintype.card (Sigma B) = Finset.univ.sum (fun a : Span => Fintype.card (B a)) := by
    simp [B]
  have hfiber_le :
      Finset.univ.sum (fun a : Span => Fintype.card (B a)) ≤
        Finset.univ.sum (fun _ : Span => 2 ^ (p - t)) := by
    refine Finset.sum_le_sum ?_
    intro a ha
    simpa [B, Vec] using F2BadTupleLastBChoicesBound p m t pref a.val
  have hsum_const :
      Finset.univ.sum (fun _ : Span => 2 ^ (p - t)) =
        Fintype.card Span * 2 ^ (p - t) := by
    simp
  calc
    Fintype.card Source ≤ Fintype.card (Sigma B) := hle_sigma
    _ = Finset.univ.sum (fun a : Span => Fintype.card (B a)) := hcard_sigma
    _ ≤ Finset.univ.sum (fun _ : Span => 2 ^ (p - t)) := hfiber_le
    _ = Fintype.card Span * 2 ^ (p - t) := hsum_const
    _ = 2 ^ t * 2 ^ (p - t) := by rw [hspan_card]
