import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Tablet.StarProductLayerChoiceMax
import Tablet.StarProductRankAtMostSet

-- [TABLET NODE: StarProductRankAtMostCardLeSuccMulLayerChoice]

universe u

theorem StarProductRankAtMostCardLeSuccMulLayerChoice (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ) :
    (StarProductRankAtMostSet K t p r).card ≤
      (r + 1) * (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card := by
-- BODY
  classical
  let U := StarProductRankAtMostSet K t p r
  let Z := fun s => StarProductRankLayer K t p s
  have hsubset : U ⊆ (Finset.Icc 0 r).biUnion Z := by
    intro y hy
    simpa [U, Z, StarProductRankAtMostSet, StarProductRankLayer] using hy
  have hU :
      U.card ≤ ((Finset.Icc 0 r).biUnion Z).card := Finset.card_le_card hsubset
  have hUnion :
      ((Finset.Icc 0 r).biUnion Z).card ≤
        (Finset.Icc 0 r).card *
          (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card := by
    refine Finset.card_biUnion_le_card_mul (Finset.Icc 0 r) Z
      (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card ?_
    intro s hs
    exact StarProductLayerChoiceMax K t p r s (Finset.mem_Icc.mp hs).2
  calc
    (StarProductRankAtMostSet K t p r).card = U.card := rfl
    _ ≤ ((Finset.Icc 0 r).biUnion Z).card := hU
    _ ≤ (Finset.Icc 0 r).card *
          (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card := hUnion
    _ = (r + 1) * (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card := by
      simp
