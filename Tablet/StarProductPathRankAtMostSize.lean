import Tablet.StarProductRankAtMostSet

-- [TABLET NODE: StarProductPathRankAtMostSize]

universe u

noncomputable def StarProductPathRankAtMostSize (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {k : ℕ}
    (v : Fin k → ProductDigraphVertex (PolarityGraph K t))
    (l : Fin (t + 1)) (i : ℕ) : ℝ := by
-- BODY
  classical
  by_cases hi : i ≤ k
  · exact
      ((StarProductRankAtMostSet K t
        (fun j : Fin i => v ⟨j.1, lt_of_lt_of_le j.2 hi⟩) l.1).card : ℝ)
  · exact 0
