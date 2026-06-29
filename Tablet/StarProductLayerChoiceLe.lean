import Tablet.StarProductLayerChoice

-- [TABLET NODE: StarProductLayerChoiceLe]

universe u

theorem StarProductLayerChoiceLe (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ) :
    StarProductLayerChoice K t p r ≤ r := by
-- BODY
  unfold StarProductLayerChoice
  exact
    (Finset.mem_Icc.mp
      (Classical.choose_spec
        (Finset.exists_max_image (Finset.Icc 0 r)
          (fun s => (StarProductRankLayer K t p s).card)
          (by exact ⟨0, by simp⟩))).1).2
