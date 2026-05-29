import Tablet.LoopGraph

-- [TABLET NODE: PolarityGraph]

universe u

noncomputable def PolarityGraph (K : Type u) [Field K] (t : ℕ) :
    LoopGraph (Projectivization K (Fin (t + 1) → K)) :=
-- BODY
  fun x y => Projectivization.orthogonal x y
