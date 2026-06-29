import Mathlib.Data.Finset.Max
import Tablet.StarProductRankLayer

-- [TABLET NODE: StarProductLayerChoice]

universe u

noncomputable def StarProductLayerChoice (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ) : ℕ :=
-- BODY
  Classical.choose
    (Finset.exists_max_image (Finset.Icc 0 r)
      (fun s => (StarProductRankLayer K t p s).card)
      (by exact ⟨0, by simp⟩))
