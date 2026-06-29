import Tablet.StarProductRankAtMostCardLeSuccMulLayerChoice

-- [TABLET NODE: StarProductLayerChoicePositive]

universe u

theorem StarProductLayerChoicePositive (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ)
    (hU : 0 < (StarProductRankAtMostSet K t p r).card) :
    0 < (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card := by
-- BODY
  have hnat := StarProductRankAtMostCardLeSuccMulLayerChoice K t p r
  by_contra hZ
  have hZzero :
      (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card = 0 :=
    Nat.eq_zero_of_not_pos hZ
  rw [hZzero, Nat.mul_zero] at hnat
  exact Nat.not_lt_zero _ (lt_of_lt_of_le hU hnat)
