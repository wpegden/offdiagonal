import Tablet.StarProductPoorChild
import Tablet.StarProductPopularChild

-- [TABLET NODE: StarProductConcreteMarked]

universe u

noncomputable def StarProductConcreteMarked (K : Type u) [Field K] (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    (ell : ∀ m : ℕ,
      (Fin m → ProductDigraphVertex (PolarityGraph K t)) → ℕ → ℕ) :
    ∀ m : ℕ,
      (Fin m → ProductDigraphVertex (PolarityGraph K t)) →
        ProductDigraphVertex (PolarityGraph K t) → Bool := by
-- BODY
  classical
  intro m p x
  exact decide
    (StarProductPrefixRank K t p x.val.2 ≤ t ∧
      (StarProductPopularChild K t q ell p x ∨
        StarProductPoorChild K t q ell p x))
