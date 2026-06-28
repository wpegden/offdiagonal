import Tablet.PolarityGraphParameters
import Tablet.ProductDigraphVertexCard

-- [TABLET NODE: StarProductPolarityVertexCountBound]

universe u

theorem StarProductPolarityVertexCountBound (K : Type u) [Field K] [Fintype K]
    (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    (hn : ((q ^ (t + 1) - 1) / (q - 1)) ≤ 2 * q ^ t)
    (hd : ((q ^ t - 1) / (q - 1)) ≤ 2 * q ^ (t - 1)) :
    Fintype.card (ProductDigraphVertex (PolarityGraph K t)) ≤
      4 * q ^ (2 * t - 1) := by
-- BODY
  classical
  let n := (q ^ (t + 1) - 1) / (q - 1)
  let d := (q ^ t - 1) / (q - 1)
  let lambda := Real.sqrt
    ((((q ^ t - 1) / (q - 1)) -
      ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ)
  have hparams : LoopGraphNdLambda (PolarityGraph K t) n d lambda := by
    simpa [n, d, lambda] using PolarityGraphParameters K t q ht hq
  have hcard :
      Fintype.card (ProductDigraphVertex (PolarityGraph K t)) = d * n :=
    ProductDigraphVertexCard (PolarityGraph K t) n d lambda hparams
  have hn' : n ≤ 2 * q ^ t := by
    simpa [n] using hn
  have hd' : d ≤ 2 * q ^ (t - 1) := by
    simpa [d] using hd
  have hprod : d * n ≤ (2 * q ^ (t - 1)) * (2 * q ^ t) :=
    Nat.mul_le_mul hd' hn'
  calc
    Fintype.card (ProductDigraphVertex (PolarityGraph K t))
        = d * n := hcard
    _ ≤ (2 * q ^ (t - 1)) * (2 * q ^ t) := hprod
    _ = 4 * q ^ (2 * t - 1) := by
      have hexp : (t - 1) + t = 2 * t - 1 := by omega
      calc
        (2 * q ^ (t - 1)) * (2 * q ^ t)
            = 4 * (q ^ (t - 1) * q ^ t) := by ring
        _ = 4 * q ^ ((t - 1) + t) := by rw [← pow_add]
        _ = 4 * q ^ (2 * t - 1) := by rw [hexp]
