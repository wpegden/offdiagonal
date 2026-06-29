import Mathlib.Tactic
import Tablet.StarProductConcreteAllChildrenBound
import Tablet.StarProductConcreteMarkedChildrenBound
import Tablet.StarProductConcretePathWeightBound
import Tablet.StarProductHLeDelta
import Tablet.StarProductMarkedTreeCountingBridge
import Tablet.StarProductPolarityParameterBounds
import Tablet.StarProductWLeK

-- [TABLET NODE: StarProductConcreteTreeCountingBound]

universe u

theorem StarProductConcreteTreeCountingBound (K : Type u)
    [Field K] [Fintype K] (t q A k w Delta : ℕ) (C : ℝ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    (hn : ((q ^ (t + 1) - 1) / (q - 1)) ≤ 2 * q ^ t)
    (hd : ((q ^ t - 1) / (q - 1)) ≤ 2 * q ^ (t - 1))
    (hDelta : 4 * q ^ (2 * t - 1) ≤ Delta)
    (hA_marked : 10128 * t ≤ A)
    (hA_delta : (A : ℝ) ≤ 4 * (q : ℝ) ^ (t - 1))
    (hA_le_C : (A : ℝ) ≤ C)
    (hlog_ge_one : 1 ≤ Real.log (q : ℝ))
    (hw : (w : ℝ) ≤ (A : ℝ) * (q : ℝ) * Real.log (q : ℝ))
    (hk : C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ))
    (hfactor :
      (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) ^ (w / (t + 1) - 1) <
        1 / (4 * (q : ℝ) ^ t)) :
    ForwardIndependentTupleCount (StarProductDigraph (PolarityGraph K t)) k ≤
      2 ^ k * Delta ^ w * (A * q ^ t) ^ (k - w) := by
-- BODY
  classical
  obtain ⟨_, hq_two, _⟩ := StarProductPolarityParameterBounds K t q ht hq
  have hq_one : 1 ≤ q := by omega
  have hh_real : ((A * q ^ t : ℕ) : ℝ) ≤ (A : ℝ) * (q : ℝ) ^ t := by
    norm_num
  have hhDelta : A * q ^ t ≤ Delta :=
    StarProductHLeDelta (A : ℝ) t q (A * q ^ t) Delta
      ht hq_one hh_real hA_delta hDelta
  have hwk : w ≤ k :=
    StarProductWLeK (A : ℝ) C q k w
      (by positivity) hA_le_C hlog_ge_one hw hk
  exact
    StarProductMarkedTreeCountingBridge (PolarityGraph K t) k w Delta (A * q ^ t)
      (StarProductConcreteMarked K t q
        (fun _ p r => StarProductLayerChoice K t p r))
      hwk hhDelta
      (by
        intro v hv
        exact StarProductConcretePathWeightBound K t q k w ht hq v hv hfactor)
      (StarProductConcreteAllChildrenBound K t q Delta k ht hq hn hd hDelta)
      (StarProductConcreteMarkedChildrenBound K t q A (A * q ^ t) k ht hq
        hA_marked (le_refl _))
