import Tablet.StarProductRankLayer

-- [TABLET NODE: StarProductPoorChild]

universe u

noncomputable def StarProductPoorChild (K : Type u) [Field K] (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    (ell : ∀ m : ℕ,
      (Fin m → ProductDigraphVertex (PolarityGraph K t)) → ℕ → ℕ)
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t)) : Prop := by
-- BODY
  classical
  let r := StarProductPrefixRank K t p x.val.2
  let Z := StarProductRankLayer K t p (ell m p r)
  exact
    ((Z.filter (fun y => PolarityGraph K t x.val.1 y)).card : ℝ) ≤
      (Z.card : ℝ) / (8 * (q : ℝ))
