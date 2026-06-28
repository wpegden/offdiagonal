import Tablet.ForwardIndependentTuple
import Tablet.StarProductDigraph

-- [TABLET NODE: StarProductForwardIndependentChildCountLeVertices]

universe u

theorem StarProductForwardIndependentChildCountLeVertices {V : Type u}
    (G : LoopGraph V) [Fintype (ProductDigraphVertex G)]
    {m : ℕ} (pref : Fin m → ProductDigraphVertex G) :
    Nat.card
      {x : ProductDigraphVertex G //
        ForwardIndependentTuple (StarProductDigraph G)
          (@Fin.snoc m (fun _ => ProductDigraphVertex G) pref x)} ≤
      Fintype.card (ProductDigraphVertex G) := by
-- BODY
  classical
  letI : Fintype
      {x : ProductDigraphVertex G //
        ForwardIndependentTuple (StarProductDigraph G)
          (@Fin.snoc m (fun _ => ProductDigraphVertex G) pref x)} :=
    Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card]
  exact Fintype.card_le_of_injective (fun x => (x : ProductDigraphVertex G))
    (by
      intro x y hxy
      exact Subtype.ext hxy)
