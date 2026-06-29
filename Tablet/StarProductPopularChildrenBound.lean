import Mathlib.Tactic
import Tablet.StarProductFullRankNoForwardIndependentExtension
import Tablet.StarProductPopularRankChildrenBound

-- [TABLET NODE: StarProductPopularChildrenBound]

universe u

theorem StarProductPopularChildrenBound (K : Type u) [Field K] [Fintype K]
    (t q k : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K) :
    ∀ (m : ℕ), m < k →
      ∀ p : Fin m → ProductDigraphVertex (PolarityGraph K t),
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) p →
          Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
            ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
              (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ∧
            StarProductPopularChild K t q
              (fun _ p r => StarProductLayerChoice K t p r) p x} ≤ 128 * t * q ^ t := by
-- BODY
  classical
  intro m _hm p _hp
  let Wv := ProductDigraphVertex (PolarityGraph K t)
  let All : Finset Wv := Finset.univ.filter (fun x : Wv =>
    ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc m (fun _ => Wv) p x) ∧
    StarProductPopularChild K t q
      (fun _ p r => StarProductLayerChoice K t p r) p x)
  let ChildRank : ℕ → Finset Wv := fun r =>
    Finset.univ.filter (fun x : Wv =>
      ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
        (@Fin.snoc m (fun _ => Wv) p x) ∧
      StarProductPopularChild K t q
        (fun _ p r => StarProductLayerChoice K t p r) p x ∧
      StarProductPrefixRank K t p x.val.2 = r)
  have hAllSub : All ⊆ (Finset.range (t + 1)).biUnion ChildRank := by
    intro x hx
    have hxFI : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
        (@Fin.snoc m (fun _ => Wv) p x) := (Finset.mem_filter.mp hx).2.1
    have hxpop : StarProductPopularChild K t q
        (fun _ p r => StarProductLayerChoice K t p r) p x :=
      (Finset.mem_filter.mp hx).2.2
    let r0 := StarProductPrefixRank K t p x.val.2
    have hrle : r0 ≤ t + 1 := by
      dsimp [r0, StarProductPrefixRank]
      simpa [Module.finrank_fintype_fun_eq_card] using
        (Submodule.finrank_le (StarProductPrefixSpan K t p x.val.2))
    have hrne : r0 ≠ t + 1 := by
      intro hr_eq
      exact (StarProductFullRankNoForwardIndependentExtension K t p x.val.2 x rfl hr_eq) hxFI
    have hrlt : r0 < t + 1 := lt_of_le_of_ne hrle hrne
    refine Finset.mem_biUnion.mpr ⟨r0, by simpa using hrlt, ?_⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hxFI, hxpop, rfl⟩
  have hAllCard : All.card ≤ ((Finset.range (t + 1)).biUnion ChildRank).card :=
    Finset.card_le_card hAllSub
  have hRankBound : ∀ r ∈ Finset.range (t + 1), (ChildRank r).card ≤ 64 * q ^ t := by
    intro r hrmem
    have hr : r ≤ t := Nat.le_of_lt_succ (Finset.mem_range.mp hrmem)
    have h := StarProductPopularRankChildrenBound K t q r p hq hr
    simpa [ChildRank, Nat.card_eq_fintype_card, Fintype.card_subtype] using h
  have hUnion :
      ((Finset.range (t + 1)).biUnion ChildRank).card ≤
        (Finset.range (t + 1)).card * (64 * q ^ t) :=
    Finset.card_biUnion_le_card_mul (Finset.range (t + 1)) ChildRank (64 * q ^ t) hRankBound
  have harith : (Finset.range (t + 1)).card * (64 * q ^ t) ≤ 128 * t * q ^ t := by
    calc
      (Finset.range (t + 1)).card * (64 * q ^ t)
          = (t + 1) * (64 * q ^ t) := by simp
      _ = (64 * (t + 1)) * q ^ t := by ring
      _ ≤ (128 * t) * q ^ t := by
            exact Nat.mul_le_mul_right (q ^ t) (by omega : 64 * (t + 1) ≤ 128 * t)
      _ = 128 * t * q ^ t := by ring
  have hnat :
      Nat.card {x : Wv //
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
          (@Fin.snoc m (fun _ => Wv) p x) ∧
        StarProductPopularChild K t q
          (fun _ p r => StarProductLayerChoice K t p r) p x} = All.card := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype]
  rw [hnat]
  exact hAllCard.trans (hUnion.trans harith)
