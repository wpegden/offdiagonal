import Tablet.StarProductPrefixSpan

-- [TABLET NODE: StarProductSubspacePoints]

universe u

noncomputable def StarProductSubspacePoints (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (y : Projectivization K (Fin (t + 1) → K)) :
    Finset (Projectivization K (Fin (t + 1) → K)) := by
-- BODY
  classical
  exact Finset.univ.filter (fun b =>
    Projectivization.rep b ∈ StarProductPrefixSpan K t p y)
