import Tablet.DigraphToGraphIndependentSetBound
import Tablet.F2ForwardIndependentNearDiagonalBound
import Tablet.SamplingKsFreeRamseyBound
import Tablet.SimpleGraphNoIndependentSetFromCountZero
import Tablet.CloseToDiagonalExponentComparison
import Tablet.CloseToDiagonalVertexCountLowerBound
import Tablet.CloseToDiagonalTargetScaleLarge
import Tablet.CloseToDiagonalZeroCountLowerBound
import Tablet.CloseToDiagonalLossFactorChoice
import Tablet.CloseToDiagonalSamplingAlgebra
import Tablet.CloseToDiagonalPositiveSamplingLowerBound

-- [TABLET NODE: CloseToDiagonalTheorem]

theorem CloseToDiagonalTheorem :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧ ∃ s0 : ℕ,
      ∀ s a : ℕ, s0 ≤ s → (a : ℝ) ≤ delta * (s : ℝ) →
        (1 - eps) * ((s : ℝ) / Real.exp 1) *
            Real.rpow 2
              (((s : ℝ) + (a : ℝ) - 1) / 2 -
                ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
          (RamseyNumber s (s + a) : ℝ) := by
-- BODY
  intro eps heps
  by_cases heps_one : 1 ≤ eps
  · refine ⟨1, by norm_num, 1, ?_⟩
    intro s a hs ha
    have hcoef_nonpos : 1 - eps ≤ 0 := by linarith
    have hscale_nonneg :
        0 ≤ ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            (((s : ℝ) + (a : ℝ) - 1) / 2 -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) := by
      exact mul_nonneg (div_nonneg (by positivity) (Real.exp_pos 1).le)
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
    have hlhs_nonpos :
        (1 - eps) * (((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            (((s : ℝ) + (a : ℝ) - 1) / 2 -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ)))) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg hcoef_nonpos hscale_nonneg
    have hramsey_nonneg : 0 ≤ (RamseyNumber s (s + a) : ℝ) := by positivity
    nlinarith [hlhs_nonpos, hramsey_nonneg]
  · have heps_lt_one : eps < 1 := lt_of_not_ge heps_one
    rcases CloseToDiagonalLossFactorChoice eps heps heps_lt_one with
      ⟨rho, eta, delta1, hrho_pos, heta_pos, hdelta1_pos, hdelta1_le, hloss⟩
    rcases F2ForwardIndependentNearDiagonalBound eta heta_pos with
      ⟨delta0, hdelta0_pos, sF, hF⟩
    let delta : ℝ := min delta0 delta1
    have hdelta_pos : 0 < delta := lt_min hdelta0_pos hdelta1_pos
    have hdelta_nonneg : 0 ≤ delta := hdelta_pos.le
    have hdelta_le_delta0 : delta ≤ delta0 := min_le_left delta0 delta1
    have hdelta_le_delta1 : delta ≤ delta1 := min_le_right delta0 delta1
    have hdelta_le_half : delta ≤ 1 / 2 := le_trans hdelta_le_delta1 hdelta1_le
    rcases CloseToDiagonalZeroCountLowerBound eps delta heps hdelta_nonneg hdelta_le_half with
      ⟨sZ, hsZ4, hZ⟩
    rcases CloseToDiagonalTargetScaleLarge eps delta heps hdelta_nonneg hdelta_le_half with
      ⟨sB, hsB4, hBlarge⟩
    rcases CloseToDiagonalVertexCountLowerBound rho hrho_pos with
      ⟨sV, hsV4, hV⟩
    refine ⟨delta, hdelta_pos, max sF (max sZ (max sB sV)), ?_⟩
    intro s a hs ha
    have hsF : sF ≤ s := le_trans (Nat.le_max_left sF (max sZ (max sB sV))) hs
    have hsZ : sZ ≤ s := by
      exact le_trans (le_trans (Nat.le_max_left sZ (max sB sV))
        (Nat.le_max_right sF (max sZ (max sB sV)))) hs
    have hsB : sB ≤ s := by
      exact le_trans (le_trans (le_trans (Nat.le_max_left sB sV)
        (Nat.le_max_right sZ (max sB sV)))
        (Nat.le_max_right sF (max sZ (max sB sV)))) hs
    have hsV : sV ≤ s := by
      exact le_trans (le_trans (le_trans (Nat.le_max_right sB sV)
        (Nat.le_max_right sZ (max sB sV)))
        (Nat.le_max_right sF (max sZ (max sB sV)))) hs
    have hs4 : 4 ≤ s := le_trans hsZ4 hsZ
    have hspos_nat : 0 < s := by omega
    have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
    have hk : 1 ≤ s + a := by omega
    have haF : (a : ℝ) ≤ delta0 * (s : ℝ) := by
      exact le_trans ha (mul_le_mul_of_nonneg_right hdelta_le_delta0 hspos.le)
    rcases hF s a hsF haF with
      ⟨W, instW, D, hloopless, hDfree, hcard, hfwi⟩
    letI : Fintype W := instW
    rcases DigraphToGraphIndependentSetBound D s (s + a) hDfree hk with
      ⟨G, hGKs, hGcount⟩
    by_cases hzero : SimpleGraphIndependentSetCount G (s + a) = 0
    · have hNoInd := SimpleGraphNoIndependentSetFromCountZero G (s + a) hzero
      have hRamseyNat :
          Fintype.card W < RamseyNumber s (s + a) :=
        RamseyNumberLowerBoundFromCounterexample G s (s + a) hGKs hNoInd
      have hRamseyReal :
          (Fintype.card W : ℝ) ≤ (RamseyNumber s (s + a) : ℝ) := by
        exact le_of_lt (by exact_mod_cast hRamseyNat)
      have hzero_bound := hZ s a hsZ ha
      have hzero_bound_card :
          (1 - eps) * ((s : ℝ) / Real.exp 1) *
              Real.rpow 2
                ((((s : ℝ) + (a : ℝ) - 1) / 2) -
                  ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
            (Fintype.card W : ℝ) := by
        simpa [hcard] using hzero_bound
      exact hzero_bound_card.trans hRamseyReal
    · have hcount_pos_nat : 0 < SimpleGraphIndependentSetCount G (s + a) :=
        Nat.pos_of_ne_zero hzero
      let E : ℝ := (3 / 2 : ℝ) * (s : ℝ) ^ 2 + (a : ℝ) * (s : ℝ) -
        (5 / 2 : ℝ) * (s : ℝ) + eta * (s : ℝ)
      let p0 : ℝ := (((s + a : ℕ) : ℝ) / Real.exp 1) *
        Real.rpow 2 (-(E / ((s + a : ℕ) : ℝ)))
      have hI_pos :
          1 ≤ ((SimpleGraphIndependentSetCount G (s + a) : ℕ) : ℝ) := by
        exact_mod_cast hcount_pos_nat
      have hF_bound :
          ((ForwardIndependentTupleCount D (s + a) : ℕ) : ℝ) ≤ Real.rpow 2 E := by
        simpa [E] using hfwi
      have hsampling_alg := CloseToDiagonalSamplingAlgebra (s + a) E
        (((SimpleGraphIndependentSetCount G (s + a) : ℕ) : ℝ))
        (((ForwardIndependentTupleCount D (s + a) : ℕ) : ℝ))
        hk hGcount hF_bound hI_pos
      have hsampling_count :
          Real.rpow p0 (((s + a : ℕ) : ℝ)) *
            ((SimpleGraphIndependentSetCount G (s + a) : ℕ) : ℝ) ≤ 1 := by
        simpa [p0] using hsampling_alg.1
      have hp0_le_one : p0 ≤ 1 := by
        simpa [p0] using hsampling_alg.2
      have hp0_nonneg : 0 ≤ p0 := by
        dsimp [p0, E]
        positivity
      have hsample :
          p0 * (Fintype.card W : ℝ) - 1 < (RamseyNumber s (s + a) : ℝ) :=
        SamplingKsFreeRamseyBound G s (s + a) p0 hGKs hk hp0_nonneg hp0_le_one
          hsampling_count
      have hsampleN :
          p0 *
              ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) -
            1 < (RamseyNumber s (s + a) : ℝ) := by
        simpa [hcard] using hsample
      have hVbound := hV s hsV
      have hBlarge_sa := hBlarge s a hsB ha
      have hpositive_lower := CloseToDiagonalPositiveSamplingLowerBound
        eps rho eta delta delta1 s a heps heps_lt_one heta_pos.le hdelta_nonneg
        hdelta_le_delta1 hloss hVbound hBlarge_sa hs4 ha
      have htarget_le :
          (1 - eps) * ((s : ℝ) / Real.exp 1) *
              Real.rpow 2
                ((((s : ℝ) + (a : ℝ) - 1) / 2) -
                  ((a : ℝ) ^ 2) / (2 * (s : ℝ))) ≤
            p0 *
                ((2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 : ℕ) : ℝ) -
              1 := by
        simpa [E, p0] using hpositive_lower
      exact le_of_lt (lt_of_le_of_lt htarget_le hsampleN)
