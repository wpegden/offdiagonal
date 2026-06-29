import Mathlib.Tactic
import Tablet.StarProductPrefixRankSnocMonotone
import Tablet.StarProductRankAtMostSet

-- [TABLET NODE: StarProductRankAtMostSetSnocSubset]

universe u

theorem StarProductRankAtMostSetSnocSubset (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (l : ℕ) :
    StarProductRankAtMostSet K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) l ⊆
      StarProductRankAtMostSet K t p l := by
-- BODY
  classical
  intro y hy
  have hnew : StarProductPrefixRank K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) y ≤ l := by
    simpa [StarProductRankAtMostSet] using hy
  have holdle := StarProductPrefixRankSnocMonotone K t p x y
  exact by
    simp [StarProductRankAtMostSet, le_trans holdle hnew]
