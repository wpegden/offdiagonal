import Mathlib.Tactic
import Tablet.ForwardIndependentTuple
import Tablet.StarProductDigraph
import Tablet.StarProductPoorChild
import Tablet.StarProductPoorRankEdgeBound

-- [TABLET NODE: StarProductPoorRankChildrenBound]

universe u

open Classical in
theorem StarProductPoorRankChildrenBound (K : Type u) [Field K] [Fintype K]
    (t q r : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (hr : r ≤ t) :
    Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
      ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ∧
      StarProductPoorChild K t q
        (fun _ p r => StarProductLayerChoice K t p r) p x ∧
      StarProductPrefixRank K t p x.val.2 = r} ≤
      5000 * q ^ t := by
-- BODY
  classical
  let V := Projectivization K (Fin (t + 1) → K)
  let G : LoopGraph V := PolarityGraph K t
  let Wv := ProductDigraphVertex (PolarityGraph K t)
  let Zell : Finset V := StarProductRankLayer K t p (StarProductLayerChoice K t p r)
  let P : Finset V := Finset.univ.filter (fun a : V =>
    ((Zell.filter (fun y => G a y)).card : ℝ) ≤
      (Zell.card : ℝ) / (8 * (q : ℝ)))
  let Zr : Finset V := StarProductRankLayer K t p r
  let Child : Finset Wv := Finset.univ.filter (fun x : Wv =>
    ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc m (fun _ => Wv) p x) ∧
    StarProductPoorChild K t q
      (fun _ p r => StarProductLayerChoice K t p r) p x ∧
    StarProductPrefixRank K t p x.val.2 = r)
  let Edge : Finset (V × V) := (P.product Zr).filter (fun z : V × V => G z.1 z.2)
  have hedgeReal :
      ((LoopGraphEdgeCountBetween G P Zr : ℕ) : ℝ) ≤ 5000 * (q : ℝ) ^ t := by
    simpa [V, G, Zell, P, Zr] using StarProductPoorRankEdgeBound K t q r ht hq p hr
  have hedgeNat : LoopGraphEdgeCountBetween G P Zr ≤ 5000 * q ^ t := by
    exact_mod_cast hedgeReal
  have hEdgeCard : Edge.card = LoopGraphEdgeCountBetween G P Zr := by
    dsimp [Edge, LoopGraphEdgeCountBetween]
  let enc : {x // x ∈ Child} → {e // e ∈ Edge} := fun x =>
    ⟨(x.1.val.1, x.1.val.2), by
      have hxmem := Finset.mem_filter.mp x.2
      have hxpoor : StarProductPoorChild K t q
          (fun _ p r => StarProductLayerChoice K t p r) p x.1 := hxmem.2.2.1
      have hxrank : StarProductPrefixRank K t p x.1.val.2 = r := hxmem.2.2.2
      have haP : x.1.val.1 ∈ P := by
        refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
        simpa [P, Zell, G, StarProductPoorChild, hxrank] using hxpoor
      have hbZ : x.1.val.2 ∈ Zr := by
        simp [Zr, StarProductRankLayer, hxrank]
      have hGxy : G x.1.val.1 x.1.val.2 := by
        simpa [G] using x.1.property
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨haP, hbZ⟩, hGxy⟩⟩
  have henc_inj : Function.Injective enc := by
    intro x y hxy
    have hval : x.1.val = y.1.val :=
      congrArg (fun z : {e // e ∈ Edge} => z.1) hxy
    apply Subtype.ext
    exact Subtype.ext hval
  have hChildCard : Child.card ≤ Edge.card := by
    simpa using Fintype.card_le_of_injective enc henc_inj
  have hnat :
      Nat.card {x : Wv //
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
          (@Fin.snoc m (fun _ => Wv) p x) ∧
        StarProductPoorChild K t q
          (fun _ p r => StarProductLayerChoice K t p r) p x ∧
        StarProductPrefixRank K t p x.val.2 = r} = Child.card := by
    rw [Nat.card_eq_fintype_card]
    rw [Fintype.card_subtype]
  rw [hnat]
  exact hChildCard.trans (by simpa [hEdgeCard] using hedgeNat)
