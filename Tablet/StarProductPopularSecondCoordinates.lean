import Tablet.StarProductLayerChoice
import Tablet.StarProductPopularChild

-- [TABLET NODE: StarProductPopularSecondCoordinates]

universe u

noncomputable def StarProductPopularSecondCoordinates (K : Type u) [Field K] (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ) :
    Finset (Projectivization K (Fin (t + 1) → K)) := by
-- BODY
  classical
  exact (StarProductRankLayer K t p r).filter (fun b =>
    ((StarProductRankLayer K t p (StarProductLayerChoice K t p r)).filter
        (fun y => Projectivization.rep b ∈ StarProductPrefixSpan K t p y)).card ≥
      ((StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card : ℝ) /
        (16 * (q : ℝ)))
