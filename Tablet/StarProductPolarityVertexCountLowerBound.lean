import Tablet.PolarityGraphParameters
import Tablet.ProductDigraphVertexCard
import Tablet.StarProductPolarityParameterBounds

-- [TABLET NODE: StarProductPolarityVertexCountLowerBound]

universe u

theorem StarProductPolarityVertexCountLowerBound (K : Type u) [Field K] [Fintype K]
    (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K) :
    ((q : ℝ) ^ (2 * t - 1)) / 4 ≤
      (Fintype.card (ProductDigraphVertex (PolarityGraph K t)) : ℝ) := by
-- BODY
  classical
  let n := (q ^ (t + 1) - 1) / (q - 1)
  let d := (q ^ t - 1) / (q - 1)
  let a := (q ^ (t - 1) - 1) / (q - 1)
  let lambda := Real.sqrt (((d - a : ℕ) : ℝ))
  have hparams_nd :
      LoopGraphNdLambda (PolarityGraph K t) n d lambda := by
    simpa [n, d, a, lambda] using PolarityGraphParameters K t q ht hq
  have hcard :
      Fintype.card (ProductDigraphVertex (PolarityGraph K t)) = d * n :=
    ProductDigraphVertexCard (PolarityGraph K t) n d lambda hparams_nd
  have hbounds := StarProductPolarityParameterBounds K t q ht hq
  have hbounds' :
      0 < q ∧ 2 ≤ q ∧ 0 < n ∧ 0 < d ∧
        q ^ t ≤ n ∧ n ≤ 2 * q ^ t ∧
        q ^ (t - 1) ≤ d ∧ d ≤ 2 * q ^ (t - 1) ∧
        (d - a : ℕ) = q ^ (t - 1) ∧
        lambda ^ 2 = ((q ^ (t - 1) : ℕ) : ℝ) := by
    simpa [n, d, a, lambda] using hbounds
  rcases hbounds' with
    ⟨_hq_pos, _hq_two, _hn_pos, _hd_pos, hn_lower, _hn_upper,
      hd_lower, _hd_upper, _hdiff, _hlambda⟩
  have hpow_mul_nat : q ^ (2 * t - 1) = q ^ (t - 1) * q ^ t := by
    have hexp : 2 * t - 1 = (t - 1) + t := by omega
    rw [hexp, pow_add]
  have hpow_le_card_nat :
      q ^ (2 * t - 1) ≤ Fintype.card (ProductDigraphVertex (PolarityGraph K t)) := by
    rw [hcard, hpow_mul_nat]
    exact Nat.mul_le_mul hd_lower hn_lower
  have hpow_le_card_real :
      (q : ℝ) ^ (2 * t - 1) ≤
        (Fintype.card (ProductDigraphVertex (PolarityGraph K t)) : ℝ) := by
    exact_mod_cast hpow_le_card_nat
  have hpow_nonneg : 0 ≤ (q : ℝ) ^ (2 * t - 1) := by positivity
  nlinarith
