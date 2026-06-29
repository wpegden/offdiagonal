import Mathlib.Tactic
import Tablet.StarProductFixedBRankLeExtensionBound
import Tablet.StarProductGeometricSumLeTwoPow
import Tablet.StarProductLayerChoiceLe
import Tablet.StarProductPopularSecondCoordinatesBound

-- [TABLET NODE: StarProductPopularRankChildrenBound]

universe u

theorem StarProductPopularRankChildrenBound (K : Type u) [Field K] [Fintype K]
    (t q r : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (hq : q = Fintype.card K) (hr : r ≤ t) :
    Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
      ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ∧
      StarProductPopularChild K t q
        (fun _ p r => StarProductLayerChoice K t p r) p x ∧
      StarProductPrefixRank K t p x.val.2 = r} ≤
      64 * q ^ t := by
-- BODY
  classical
  let V := Projectivization K (Fin (t + 1) → K)
  let Wv := ProductDigraphVertex (PolarityGraph K t)
  let Child : Finset Wv := Finset.univ.filter (fun x : Wv =>
    ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc m (fun _ => Wv) p x) ∧
    StarProductPopularChild K t q
      (fun _ p r => StarProductLayerChoice K t p r) p x ∧
    StarProductPrefixRank K t p x.val.2 = r)
  let Bpop := StarProductPopularSecondCoordinates K t q p r
  let ChildOfB : V → Finset Wv := fun b =>
    Finset.univ.filter (fun x : Wv =>
      ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
        (@Fin.snoc m (fun _ => Wv) p x) ∧ x.val.2 = b)
  have hgeom :
      (∑ i ∈ Finset.range (t + 1 - r), q ^ i) ≤ 2 * q ^ (t - r) := by
    have h := StarProductGeometricSumLeTwoPow K q (t - r) hq
    have hidx : t + 1 - r = (t - r) + 1 := by omega
    simpa [hidx] using h
  have hChildOfB : ∀ b ∈ Bpop, (ChildOfB b).card ≤ 2 * q ^ (t - r) := by
    intro b hb
    have hbrank : StarProductPrefixRank K t p b = r := by
      have hbLayer := (Finset.mem_filter.mp hb).1
      simpa [Bpop, StarProductPopularSecondCoordinates, StarProductRankLayer] using hbLayer
    let Ext : Finset V := Finset.univ.filter (fun a : V =>
      ∃ x : Wv, x.val.1 = a ∧ x.val.2 = b ∧
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
          (@Fin.snoc m (fun _ => Wv) p x))
    have hExtSpec : ∀ a ∈ Ext, ∃ x : Wv, x.val.1 = a ∧ x.val.2 = b ∧
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
          (@Fin.snoc m (fun _ => Wv) p x) := by
      intro a ha
      exact (Finset.mem_filter.mp ha).2
    have hfixed :
        Ext.card ≤ 2 * q ^ (t - r) :=
      StarProductFixedBRankLeExtensionBound K t q r p b hq hbrank hr hgeom Ext hExtSpec
    let enc : ChildOfB b → Ext := fun x =>
      ⟨x.1.val.1, by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        exact ⟨x.1, rfl, (Finset.mem_filter.mp x.2).2.2, (Finset.mem_filter.mp x.2).2.1⟩⟩
    have henc_inj : Function.Injective enc := by
      intro x y hxy
      apply Subtype.ext
      have ha : x.1.val.1 = y.1.val.1 := by
        exact congrArg Subtype.val hxy
      have hxb : x.1.val.2 = b := (Finset.mem_filter.mp x.2).2.2
      have hyb : y.1.val.2 = b := (Finset.mem_filter.mp y.2).2.2
      apply Subtype.ext
      exact Prod.ext ha (hxb.trans hyb.symm)
    have hcard : (ChildOfB b).card ≤ Ext.card := by
      simpa using Fintype.card_le_of_injective enc henc_inj
    exact hcard.trans hfixed
  have hChildSub : Child ⊆ Bpop.biUnion ChildOfB := by
    intro x hx
    have hxFI : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
        (@Fin.snoc m (fun _ => Wv) p x) := (Finset.mem_filter.mp hx).2.1
    have hxpop : StarProductPopularChild K t q
        (fun _ p r => StarProductLayerChoice K t p r) p x :=
      (Finset.mem_filter.mp hx).2.2.1
    have hxrank : StarProductPrefixRank K t p x.val.2 = r :=
      (Finset.mem_filter.mp hx).2.2.2
    have hbmem : x.val.2 ∈ Bpop := by
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · simp [StarProductRankLayer, hxrank]
      · simpa [StarProductPopularChild, hxrank] using hxpop
    refine Finset.mem_biUnion.mpr ⟨x.val.2, hbmem, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxFI, rfl⟩
  have hChildCard : Child.card ≤ (Bpop.biUnion ChildOfB).card :=
    Finset.card_le_card hChildSub
  have hUnion : (Bpop.biUnion ChildOfB).card ≤ Bpop.card * (2 * q ^ (t - r)) :=
    Finset.card_biUnion_le_card_mul Bpop ChildOfB (2 * q ^ (t - r)) hChildOfB
  have hBpop := StarProductPopularSecondCoordinatesBound K t q p r hq
  have hell : StarProductLayerChoice K t p r ≤ r :=
    StarProductLayerChoiceLe K t p r
  have hqpos : 0 < q := by
    rw [hq]
    exact Fintype.card_pos
  have hpow_le : q ^ (StarProductLayerChoice K t p r) ≤ q ^ r :=
    Nat.pow_le_pow_right hqpos hell
  have hmul_pow : q ^ (StarProductLayerChoice K t p r) * q ^ (t - r) ≤
      q ^ r * q ^ (t - r) :=
    Nat.mul_le_mul_right (q ^ (t - r)) hpow_le
  have harith :
      Bpop.card * (2 * q ^ (t - r)) ≤ 64 * q ^ t := by
    calc
      Bpop.card * (2 * q ^ (t - r))
          ≤ (32 * q ^ (StarProductLayerChoice K t p r)) * (2 * q ^ (t - r)) := by
            exact Nat.mul_le_mul_right (2 * q ^ (t - r)) hBpop
      _ = 64 * (q ^ (StarProductLayerChoice K t p r) * q ^ (t - r)) := by ring
      _ ≤ 64 * (q ^ r * q ^ (t - r)) := by
            exact Nat.mul_le_mul_left 64 hmul_pow
      _ = 64 * q ^ t := by
            have hrt : r + (t - r) = t := by omega
            rw [← pow_add, hrt]
  have hnat :
      Nat.card {x : Wv //
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
          (@Fin.snoc m (fun _ => Wv) p x) ∧
        StarProductPopularChild K t q
          (fun _ p r => StarProductLayerChoice K t p r) p x ∧
        StarProductPrefixRank K t p x.val.2 = r} = Child.card := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype]
  rw [hnat]
  simpa [Child] using hChildCard.trans (hUnion.trans harith)
