import Mathlib.Tactic
import Tablet.StarProductConcreteTreeCountingBound
import Tablet.StarProductDeltaPowerLeQPower
import Tablet.StarProductFinalNumericalAbsorption
import Tablet.StarProductFloorWeightSideConditions
import Tablet.StarProductQPowerLeTwoPow

-- [TABLET NODE: StarProductAbsorbedTreeCountingBound]

universe u

theorem StarProductAbsorbedTreeCountingBound (K : Type u)
    [Field K] [Fintype K] (t q A k : ℕ) (C : ℝ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    (hn : ((q ^ (t + 1) - 1) / (q - 1)) ≤ 2 * q ^ t)
    (hd : ((q ^ t - 1) / (q - 1)) ≤ 2 * q ^ (t - 1))
    (hA_marked : 10128 * t ≤ A)
    (hA_delta : (A : ℝ) ≤ 4 * (q : ℝ) ^ (t - 1))
    (hA_le_C : (A : ℝ) ≤ C)
    (hlog_ge_one : 1 ≤ Real.log (q : ℝ))
    (hscale : 2 * (t : ℝ) * (A : ℝ) ≤ C * Real.log 2)
    (hC_absorb : 4 * (A : ℝ) ≤ C)
    (hB_ge_one : 1 ≤ (A : ℝ) * (q : ℝ) ^ t)
    (hq_four : 4 ≤ q)
    (hk : C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ))
    (hexp :
      32 * (t : ℝ) * (q : ℝ) * Real.log (4 * (q : ℝ) ^ t) <
        ((Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ)) /
            (t + 1) - 1 : ℕ) : ℝ)) :
    ((ForwardIndependentTupleCount (StarProductDigraph (PolarityGraph K t)) k : ℕ) : ℝ) ≤
      (C * (q : ℝ) ^ t) ^ k := by
-- BODY
  classical
  let w : ℕ := Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ))
  let Delta : ℕ := 4 * q ^ (2 * t - 1)
  have ht_one : 1 ≤ t := by omega
  have hq_one : 1 ≤ q := by omega
  have hfloor :
      (w : ℝ) ≤ (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) ∧
        (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) ^ (w / (t + 1) - 1) <
          1 / (4 * (q : ℝ) ^ t) := by
    simpa [w] using StarProductFloorWeightSideConditions A t q ht_one hq_one hexp
  rcases hfloor with ⟨hw, hfactor⟩
  have htree_nat :
      ForwardIndependentTupleCount (StarProductDigraph (PolarityGraph K t)) k ≤
        2 ^ k * Delta ^ w * (A * q ^ t) ^ (k - w) := by
    exact
      StarProductConcreteTreeCountingBound K t q A k w Delta C ht hq hn hd
        (by simp [Delta]) hA_marked hA_delta hA_le_C hlog_ge_one hw hk hfactor
  have htree_real :
      ((ForwardIndependentTupleCount (StarProductDigraph (PolarityGraph K t)) k : ℕ) : ℝ) ≤
        (2 : ℝ) ^ k *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
          ((A : ℝ) * (q : ℝ) ^ t) ^ (k - w) := by
    have hcast :
        ((ForwardIndependentTupleCount (StarProductDigraph (PolarityGraph K t)) k : ℕ) : ℝ) ≤
          ((2 ^ k * Delta ^ w * (A * q ^ t) ^ (k - w) : ℕ) : ℝ) := by
      exact_mod_cast htree_nat
    calc
      ((ForwardIndependentTupleCount (StarProductDigraph (PolarityGraph K t)) k : ℕ) : ℝ)
          ≤ ((2 ^ k * Delta ^ w * (A * q ^ t) ^ (k - w) : ℕ) : ℝ) := hcast
      _ =
          (2 : ℝ) ^ k *
            (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
            ((A : ℝ) * (q : ℝ) ^ t) ^ (k - w) := by
        simp [Delta]
  have hDeltaPow :
      (4 * (q : ℝ) ^ (2 * t - 1)) ^ w ≤ (q : ℝ) ^ (2 * t * w) :=
    StarProductDeltaPowerLeQPower t q w ht_one hq_four
  have hqpow : (q : ℝ) ^ (2 * t * w) ≤ (2 : ℝ) ^ k :=
    StarProductQPowerLeTwoPow (A : ℝ) C t q k w
      (by positivity) hscale (by omega) hw hk
  have habsorbed :
      (2 : ℝ) ^ k *
          (4 * (q : ℝ) ^ (2 * t - 1)) ^ w *
          ((A : ℝ) * (q : ℝ) ^ t) ^ (k - w) ≤
        (C * (q : ℝ) ^ t) ^ k :=
    StarProductFinalNumericalAbsorption (A : ℝ) C t q k w ht_one
      (by positivity) hB_ge_one hDeltaPow hqpow hC_absorb
  exact htree_real.trans habsorbed
