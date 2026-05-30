import Mathlib.LinearAlgebra.Projectivization.Cardinality
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
  · rw [← Nat.card_eq_fintype_card]
    rw [Projectivization.card'']
    rw [Nat.card_eq_fintype_card (α := Fin (t + 1) → K),
      Nat.card_eq_fintype_card (α := K), Fintype.card_fun, Fintype.card_fin]
    rw [← hq]
  constructor
  · dsimp [LoopGraphSymmetric, PolarityGraph]
    intro x y hxy
    exact Projectivization.orthogonal_comm.mp hxy
  constructor
  · classical
    intro v
    induction v using Projectivization.ind with
    | h x hx =>
      dsimp [LoopGraphDegree, PolarityGraph]
      have hsub :
          ({ w : Projectivization K (Fin (t + 1) → K) |
            Projectivization.orthogonal (Projectivization.mk K x hx) w } :
              Finset (Projectivization K (Fin (t + 1) → K))).card =
            Fintype.card
              { w : Projectivization K (Fin (t + 1) → K) //
                Projectivization.orthogonal (Projectivization.mk K x hx) w } := by
        simpa using (Fintype.card_subtype
          (fun w : Projectivization K (Fin (t + 1) → K) =>
            Projectivization.orthogonal (Projectivization.mk K x hx) w)).symm
      refine hsub.trans ?_
      change Fintype.card
          { w : Projectivization K (Fin (t + 1) → K) //
            Projectivization.orthogonal (Projectivization.mk K x hx) w } =
        ((q ^ t - 1) / (q - 1))
      sorry
  constructor
  · sorry
  · exact Real.sqrt_nonneg _
