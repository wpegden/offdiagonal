import Tablet.DigraphToGraphIndependentSetBound
import Tablet.F2ForwardIndependentLinearBound
import Tablet.SamplingKsFreeRamseyBound
import Tablet.SimpleGraphNoIndependentSetFromCountZero
import Tablet.RamseyNumberLowerBoundFromCounterexample
import Tablet.CloseToDiagonalSamplingAlgebra
import Tablet.LinearOffDiagonalVertexCountDominates
import Tablet.LinearOffDiagonalSamplingLowerBound

-- [TABLET NODE: LinearOffDiagonalTheorem]

theorem LinearOffDiagonalTheorem :
    ∀ C : ℝ, 1 < C → ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) ≤
        (RamseyNumber s (Nat.ceil (C * (s : ℝ))) : ℝ) := by
-- BODY
  classical
  intro C hC
  rcases F2ForwardIndependentLinearBound C hC with ⟨sF, hF⟩
  rcases LinearOffDiagonalVertexCountDominates C hC with ⟨sZ, hZ⟩
  rcases LinearOffDiagonalSamplingLowerBound C hC with ⟨sP, hP⟩
  refine ⟨max sF (max sZ (max sP 1)), ?_⟩
  intro s hs
  let k : ℕ := Nat.ceil (C * (s : ℝ))
  have hsF : sF ≤ s := le_trans (Nat.le_max_left sF (max sZ (max sP 1))) hs
  have hsZ : sZ ≤ s := by
    exact le_trans (le_trans (Nat.le_max_left sZ (max sP 1))
      (Nat.le_max_right sF (max sZ (max sP 1)))) hs
  have hsP : sP ≤ s := by
    exact le_trans (le_trans (le_trans (Nat.le_max_left sP 1)
      (Nat.le_max_right sZ (max sP 1)))
      (Nat.le_max_right sF (max sZ (max sP 1)))) hs
  have hs1 : 1 ≤ s := by
    exact le_trans (le_trans (le_trans (Nat.le_max_right sP 1)
      (Nat.le_max_right sZ (max sP 1)))
      (Nat.le_max_right sF (max sZ (max sP 1)))) hs
  have hCpos : 0 < C := lt_trans (by norm_num) hC
  have hk : 1 ≤ k := by
    dsimp [k]
    rw [Nat.one_le_ceil_iff]
    exact mul_pos hCpos (by exact_mod_cast hs1)
  rcases hF s hsF with ⟨W, instW, D, _hloopless, hDfree, hcard, hfwi⟩
  letI : Fintype W := instW
  rcases DigraphToGraphIndependentSetBound D s k hDfree hk with
    ⟨G, hGKs, hGcount⟩
  by_cases hzero : SimpleGraphIndependentSetCount G k = 0
  · have hNoInd := SimpleGraphNoIndependentSetFromCountZero G k hzero
    have hRamseyNat :
        Fintype.card W < RamseyNumber s k :=
      RamseyNumberLowerBoundFromCounterexample G s k hGKs hNoInd
    have hRamseyReal :
        (Fintype.card W : ℝ) ≤ (RamseyNumber s k : ℝ) := by
      exact le_of_lt (by exact_mod_cast hRamseyNat)
    have hzero_bound := hZ s hsZ
    have hzero_bound_card :
        Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) ≤
          (Fintype.card W : ℝ) := by
      simpa [k, hcard] using hzero_bound
    exact hzero_bound_card.trans hRamseyReal
  · have hcount_pos_nat : 0 < SimpleGraphIndependentSetCount G k :=
      Nat.pos_of_ne_zero hzero
    let E : ℝ := (s : ℝ) * (k : ℝ) + (s : ℝ) ^ 2 / 2
    let p0 : ℝ := ((k : ℝ) / Real.exp 1) * Real.rpow 2 (-(E / (k : ℝ)))
    have hI_pos :
        1 ≤ ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) := by
      exact_mod_cast hcount_pos_nat
    have hF_bound :
        ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤ Real.rpow 2 E := by
      simpa [k, E] using hfwi
    have hsampling_alg := CloseToDiagonalSamplingAlgebra k E
      (((SimpleGraphIndependentSetCount G k : ℕ) : ℝ))
      (((ForwardIndependentTupleCount D k : ℕ) : ℝ))
      hk hGcount hF_bound hI_pos
    have hsampling_count :
        Real.rpow p0 (k : ℝ) *
          ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) ≤ 1 := by
      simpa [p0] using hsampling_alg.1
    have hp0_le_one : p0 ≤ 1 := by
      simpa [p0] using hsampling_alg.2
    have hp0_nonneg : 0 ≤ p0 := by
      dsimp [p0, E]
      positivity
    have hsample :
        p0 * (Fintype.card W : ℝ) - 1 < (RamseyNumber s k : ℝ) :=
      SamplingKsFreeRamseyBound G s k p0 hGKs hk hp0_nonneg hp0_le_one
        hsampling_count
    have hpositive_bound := hP s hsP
    have htarget_le :
        Real.rpow 2 ((1 - 1 / (2 * C)) * (s : ℝ)) ≤
          p0 * (Fintype.card W : ℝ) - 1 := by
      simpa [k, E, p0, hcard] using hpositive_bound
    exact le_of_lt (lt_of_le_of_lt htarget_le hsample)
