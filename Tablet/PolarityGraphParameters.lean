import Tablet.LoopGraphNdLambda
import Tablet.PolarityGraph

-- [TABLET NODE: PolarityGraphParameters]

universe u

theorem PolarityGraphParameters (K : Type u) [Field K] [Fintype K] (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K) :
    LoopGraphNdLambda (PolarityGraph K t)
      ((q ^ (t + 1) - 1) / (q - 1))
      ((q ^ t - 1) / (q - 1))
      (Real.sqrt
        ((((q ^ t - 1) / (q - 1)) -
          ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ)) := by
-- BODY
  dsimp [LoopGraphNdLambda]
  constructor
  · sorry
  constructor
  · dsimp [LoopGraphSymmetric, PolarityGraph]
    intro x y hxy
    exact Projectivization.orthogonal_comm.mp hxy
  constructor
  · sorry
  constructor
  · sorry
  · exact Real.sqrt_nonneg _
