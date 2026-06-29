import Tablet.StarProductLayerChoice

-- [TABLET NODE: StarProductLayerChoiceMax]

universe u

theorem StarProductLayerChoiceMax (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r s : ℕ)
    (hs : s ≤ r) :
    (StarProductRankLayer K t p s).card ≤
      (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card := by
-- BODY
  unfold StarProductLayerChoice
  exact
    (Classical.choose_spec
      (Finset.exists_max_image (Finset.Icc 0 r)
        (fun s => (StarProductRankLayer K t p s).card)
        (by exact ⟨0, by simp⟩))).2 s (by simp [hs])
