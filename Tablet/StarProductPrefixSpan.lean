import Tablet.ProductDigraphVertex
import Tablet.PolarityGraph

-- [TABLET NODE: StarProductPrefixSpan]

universe u

noncomputable def StarProductPrefixSpan (K : Type u) [Field K] (t : ℕ)
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (y : Projectivization K (Fin (t + 1) → K)) :
    Submodule K (Fin (t + 1) → K) := by
-- BODY
  classical
  exact Submodule.span K
    {v : Fin (t + 1) → K |
      ∃ i : Fin m,
        PolarityGraph K t (p i).val.1 y ∧
          v = Projectivization.rep (p i).val.2}
