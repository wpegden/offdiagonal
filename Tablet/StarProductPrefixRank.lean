import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Tablet.StarProductPrefixSpan

-- [TABLET NODE: StarProductPrefixRank]

universe u

noncomputable def StarProductPrefixRank (K : Type u) [Field K] (t : ℕ)
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (y : Projectivization K (Fin (t + 1) → K)) : ℕ := by
-- BODY
  exact Module.finrank K (StarProductPrefixSpan K t p y)
