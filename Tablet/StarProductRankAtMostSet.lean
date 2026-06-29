import Tablet.StarProductPrefixRank

-- [TABLET NODE: StarProductRankAtMostSet]

universe u

noncomputable def StarProductRankAtMostSet (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ) :
    Finset (Projectivization K (Fin (t + 1) → K)) := by
-- BODY
  classical
  exact Finset.univ.filter (fun y => StarProductPrefixRank K t p y ≤ r)
