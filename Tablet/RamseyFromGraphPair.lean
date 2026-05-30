import Tablet.DigraphToGraphIndependentSetBound
import Tablet.ProductDigraphForwardIndependentBound
import Tablet.SamplingKsFreeRamseyBound

-- [TABLET NODE: RamseyFromGraphPair]

universe u

theorem RamseyFromGraphPair {V : Type u} [Fintype V]
    (F G : LoopGraph V) (s n dF dG k : ℕ) (lambdaF lambdaG eta w : ℝ)
    (hs : 3 ≤ s) (hn : 3 ≤ n) (hdG : 0 < dG) (hk : 1 ≤ k)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hFG : HsFreePair F G s)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (hw : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ))
    (heta_lower : 1 / (n : ℝ) ^ 2 ≤ eta) (heta_upper : eta ≤ 1) :
    ((w ≤ (k : ℝ) ∧ (k : ℝ) ≤ eta * (dF : ℝ) * (n : ℝ)) →
      (1 / 50 : ℝ) * (k : ℝ) *
          Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) - 1 ≤
        (RamseyNumber s k : ℝ)) ∧
      (((k : ℝ) ≤ eta * (dF : ℝ) * (n : ℝ) ∧
          (100 : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 / (dG : ℝ) ≤
            (k : ℝ)) →
        (k : ℝ) / (100 * eta) - 1 ≤ (RamseyNumber s k : ℝ)) := by
-- BODY
  classical
  constructor
  · intro hkRange
    have hn_pos : 0 < n := by omega
    have hk_pos : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
    have hnR_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn_pos
    have hkR_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk_pos
    have heta_pos : 0 < eta := by
      have hbase : (0 : ℝ) < 1 / (n : ℝ) ^ 2 := by positivity
      exact lt_of_lt_of_le hbase heta_lower
    have heta_nonneg : 0 ≤ eta := le_of_lt heta_pos
    have hdF : 0 < dF := by
      by_contra hnot
      have hdF_zero : dF = 0 := Nat.eq_zero_of_not_pos hnot
      have hk_le_zero : (k : ℝ) ≤ 0 := by
        simpa [hdF_zero] using hkRange.2
      linarith
    rcases ProductDigraphForwardIndependentBound
        F G s n dF dG lambdaF lambdaG eta w
        hs hn hdF hdG hF hG hFG heta hw heta_nonneg heta_upper with
      ⟨W, hWfintype, D, hD_transitive_free, hW_card, hD_count_bound⟩
    letI : Fintype W := hWfintype
    rcases DigraphToGraphIndependentSetBound D s k hD_transitive_free hk with
      ⟨Gamma, hGamma_KsFree, hGamma_count_from_D⟩
    let B : ℝ :=
      (Real.exp 1 / (k : ℝ)) ^ k *
        ((16 : ℝ) ^ k * Real.rpow eta ((k : ℝ) - w) *
          ((dF * n : ℕ) : ℝ) ^ k)
    let p : ℝ := Real.rpow B (-(1 : ℝ) / (k : ℝ))
    have hDk_count_bound :
        ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤
          (16 : ℝ) ^ k * Real.rpow eta ((k : ℝ) - w) *
            ((dF * n : ℕ) : ℝ) ^ k :=
      hD_count_bound k hkRange.1
    have hGamma_count_bound :
        ((SimpleGraphIndependentSetCount Gamma k : ℕ) : ℝ) ≤ B := by
      have hcoef_nonneg : 0 ≤ (Real.exp 1 / (k : ℝ)) ^ k := by positivity
      calc
        ((SimpleGraphIndependentSetCount Gamma k : ℕ) : ℝ)
            ≤ (Real.exp 1 / (k : ℝ)) ^ k *
                ((ForwardIndependentTupleCount D k : ℕ) : ℝ) :=
              hGamma_count_from_D
        _ ≤ (Real.exp 1 / (k : ℝ)) ^ k *
              ((16 : ℝ) ^ k * Real.rpow eta ((k : ℝ) - w) *
                ((dF * n : ℕ) : ℝ) ^ k) := by
              exact mul_le_mul_of_nonneg_left hDk_count_bound hcoef_nonneg
        _ = B := by rfl
    have hB_pos : 0 < B := by
      have hM_pos : (0 : ℝ) < ((dF * n : ℕ) : ℝ) := by
        exact_mod_cast Nat.mul_pos hdF hn_pos
      dsimp [B]
      positivity
    have hp_pos : 0 < p := by
      dsimp [p]
      exact Real.rpow_pos_of_pos hB_pos (-(1 : ℝ) / (k : ℝ))
    have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
    have hp_pow_mul_B :
        Real.rpow p (k : ℝ) * B = 1 := by
      have hB_nonneg : 0 ≤ B := le_of_lt hB_pos
      have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
      calc
        Real.rpow p (k : ℝ) * B
            = Real.rpow B ((-(1 : ℝ) / (k : ℝ)) * (k : ℝ)) * B := by
                dsimp [p]
                rw [Real.rpow_mul hB_nonneg]
        _ = Real.rpow B (-1) * B := by
                field_simp [hkR_ne]
        _ = B⁻¹ * B := by
                have hneg : Real.rpow B (-1) = B⁻¹ := by
                  simpa [Real.rpow_one] using
                    (Real.rpow_neg (x := B) hB_nonneg (1 : ℝ))
                rw [hneg]
        _ = 1 := by
                field_simp [ne_of_gt hB_pos]
    have hsampling_count :
        Real.rpow p (k : ℝ) *
            ((SimpleGraphIndependentSetCount Gamma k : ℕ) : ℝ) ≤ 1 := by
      have hp_pow_nonneg : 0 ≤ Real.rpow p (k : ℝ) :=
        le_of_lt (Real.rpow_pos_of_pos hp_pos (k : ℝ))
      calc
        Real.rpow p (k : ℝ) *
            ((SimpleGraphIndependentSetCount Gamma k : ℕ) : ℝ)
            ≤ Real.rpow p (k : ℝ) * B := by
                exact mul_le_mul_of_nonneg_left hGamma_count_bound hp_pow_nonneg
        _ = 1 := hp_pow_mul_B
    sorry
  · intro hkRange
    sorry
