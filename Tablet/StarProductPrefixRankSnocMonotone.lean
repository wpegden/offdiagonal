import Tablet.StarProductPrefixRank
import Tablet.StarProductPrefixSpanSnocLe

-- [TABLET NODE: StarProductPrefixRankSnocMonotone]

universe u

theorem StarProductPrefixRankSnocMonotone (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (y : Projectivization K (Fin (t + 1) → K)) :
    StarProductPrefixRank K t p y ≤
      StarProductPrefixRank K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) y := by
-- BODY
  simpa [StarProductPrefixRank] using
    (Submodule.finrank_mono (StarProductPrefixSpanSnocLe K t p x y))
