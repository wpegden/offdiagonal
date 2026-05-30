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
    have hM_pos : (0 : ℝ) < ((dF * n : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos hdF hn_pos
    have hM_cast :
        ((dF * n : ℕ) : ℝ) = (dF : ℝ) * (n : ℝ) := by
      norm_num
    have hk_le_etaM :
        (k : ℝ) ≤ eta * ((dF * n : ℕ) : ℝ) := by
      simpa [hM_cast, mul_assoc] using hkRange.2
    have hetaM_div_k_ge_one :
        1 ≤ eta * ((dF * n : ℕ) : ℝ) / (k : ℝ) := by
      rw [le_div_iff₀ hkR_pos]
      simpa using hk_le_etaM
    let C : ℝ :=
      (16 : ℝ) * Real.exp 1 *
        (eta * ((dF * n : ℕ) : ℝ) / (k : ℝ))
    have hC_ge_one : 1 ≤ C := by
      have h16_ge_one : (1 : ℝ) ≤ 16 := by norm_num
      have hexp_ge_one : (1 : ℝ) ≤ Real.exp 1 :=
        Real.one_le_exp (by norm_num)
      have h16exp_ge_one : (1 : ℝ) ≤ (16 : ℝ) * Real.exp 1 := by
        calc
          (1 : ℝ) = 1 * 1 := by ring
          _ ≤ (16 : ℝ) * Real.exp 1 := by
            exact mul_le_mul h16_ge_one hexp_ge_one (by norm_num) (by norm_num)
      have hetaM_div_nonneg :
          0 ≤ eta * ((dF * n : ℕ) : ℝ) / (k : ℝ) := by positivity
      calc
        (1 : ℝ) = 1 * 1 := by ring
        _ ≤ ((16 : ℝ) * Real.exp 1) *
              (eta * ((dF * n : ℕ) : ℝ) / (k : ℝ)) := by
            exact mul_le_mul h16exp_ge_one hetaM_div_k_ge_one
              (by norm_num) (by positivity)
        _ = C := by ring
    have hCpow_ge_one : (1 : ℝ) ≤ C ^ k := by
      simpa using pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) hC_ge_one k
    have heta_pow_le :
        eta ^ k ≤ Real.rpow eta ((k : ℝ) - w) := by
      have hw_nonneg : 0 ≤ w := by
        have hnR_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
          exact_mod_cast (by omega : 1 ≤ n)
        rw [hw]
        positivity
      have hkw_le : (k : ℝ) - w ≤ (k : ℝ) := by linarith
      calc
        eta ^ k = Real.rpow eta (k : ℝ) := by
          exact (Real.rpow_natCast eta k).symm
        _ ≤ Real.rpow eta ((k : ℝ) - w) :=
          Real.rpow_le_rpow_of_exponent_ge heta_pos heta_upper hkw_le
    have hCpow_eq :
        C ^ k =
          (Real.exp 1 / (k : ℝ)) ^ k *
            ((16 : ℝ) ^ k * eta ^ k *
              ((dF * n : ℕ) : ℝ) ^ k) := by
      dsimp [C]
      field_simp [ne_of_gt hkR_pos]
      ring
    have hCpow_le_B : C ^ k ≤ B := by
      rw [hCpow_eq]
      dsimp [B]
      have hcoef_nonneg : 0 ≤ (Real.exp 1 / (k : ℝ)) ^ k := by positivity
      have h16pow_nonneg : 0 ≤ (16 : ℝ) ^ k := by positivity
      have hMpow_nonneg : 0 ≤ ((dF * n : ℕ) : ℝ) ^ k := by positivity
      apply mul_le_mul_of_nonneg_left ?_ hcoef_nonneg
      apply mul_le_mul_of_nonneg_right ?_ hMpow_nonneg
      exact mul_le_mul_of_nonneg_left heta_pow_le h16pow_nonneg
    have hB_ge_one : (1 : ℝ) ≤ B :=
      hCpow_ge_one.trans hCpow_le_B
    have hp_le_one : p ≤ 1 := by
      dsimp [p]
      exact Real.rpow_le_one_of_one_le_of_nonpos hB_ge_one
        (by
          have hdiv_nonneg : 0 ≤ (1 : ℝ) / (k : ℝ) := by positivity
          rw [neg_div]
          exact neg_nonpos.mpr hdiv_nonneg)
    have hsampling :
        p * (Fintype.card W : ℝ) - 1 < (RamseyNumber s k : ℝ) :=
      SamplingKsFreeRamseyBound Gamma s k p hGamma_KsFree hk hp_nonneg hp_le_one
        hsampling_count
    have hsampling_M :
        p * ((dF * n : ℕ) : ℝ) - 1 < (RamseyNumber s k : ℝ) := by
      simpa [hW_card] using hsampling
    let M : ℝ := ((dF * n : ℕ) : ℝ)
    let A : ℝ := (Real.exp 1 / (k : ℝ)) * (16 : ℝ) * M
    have hA_pos : 0 < A := by
      dsimp [A, M]
      positivity
    have hB_eq :
        B = Real.rpow A (k : ℝ) * Real.rpow eta ((k : ℝ) - w) := by
      dsimp [B, A, M]
      rw [Real.rpow_natCast]
      field_simp [ne_of_gt hkR_pos]
      ring
    have hA_rpow_part :
        Real.rpow (Real.rpow A (k : ℝ)) (-(1 : ℝ) / (k : ℝ)) = A⁻¹ := by
      have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
      calc
        Real.rpow (Real.rpow A (k : ℝ)) (-(1 : ℝ) / (k : ℝ))
            = Real.rpow A ((k : ℝ) * (-(1 : ℝ) / (k : ℝ))) :=
              (Real.rpow_mul (le_of_lt hA_pos) (k : ℝ) (-(1 : ℝ) / (k : ℝ))).symm
        _ = Real.rpow A (-1) := by
              field_simp [hkR_ne]
        _ = A⁻¹ := by
              have hA_nonneg : 0 ≤ A := le_of_lt hA_pos
              have hneg : Real.rpow A (-1) = A⁻¹ := by
                simpa [Real.rpow_one] using
                  (Real.rpow_neg (x := A) hA_nonneg (1 : ℝ))
              exact hneg
    have heta_rpow_part :
        Real.rpow (Real.rpow eta ((k : ℝ) - w)) (-(1 : ℝ) / (k : ℝ)) =
          Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) := by
      have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
      calc
        Real.rpow (Real.rpow eta ((k : ℝ) - w)) (-(1 : ℝ) / (k : ℝ))
            = Real.rpow eta (((k : ℝ) - w) * (-(1 : ℝ) / (k : ℝ))) :=
              (Real.rpow_mul (le_of_lt heta_pos) ((k : ℝ) - w)
                (-(1 : ℝ) / (k : ℝ))).symm
        _ = Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) := by
              congr 1
              field_simp [hkR_ne]
              ring
    have hp_eq :
        p = A⁻¹ * Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) := by
      calc
        p = Real.rpow B (-(1 : ℝ) / (k : ℝ)) := by rfl
        _ = Real.rpow
              (Real.rpow A (k : ℝ) * Real.rpow eta ((k : ℝ) - w))
              (-(1 : ℝ) / (k : ℝ)) := by
              rw [hB_eq]
        _ = Real.rpow (Real.rpow A (k : ℝ)) (-(1 : ℝ) / (k : ℝ)) *
              Real.rpow (Real.rpow eta ((k : ℝ) - w)) (-(1 : ℝ) / (k : ℝ)) := by
              exact Real.mul_rpow
                (x := Real.rpow A (k : ℝ))
                (y := Real.rpow eta ((k : ℝ) - w))
                (z := -(1 : ℝ) / (k : ℝ))
                (le_of_lt (Real.rpow_pos_of_pos hA_pos (k : ℝ)))
                (le_of_lt (Real.rpow_pos_of_pos heta_pos ((k : ℝ) - w)))
        _ = A⁻¹ * Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) := by
              rw [hA_rpow_part, heta_rpow_part]
    have hpM_eq :
        p * M =
          ((k : ℝ) / ((16 : ℝ) * Real.exp 1)) *
            Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) := by
      rw [hp_eq]
      dsimp [A]
      field_simp [ne_of_gt hkR_pos, ne_of_gt hM_pos, Real.exp_ne_zero 1]
      exact mul_inv_cancel₀ (ne_of_gt hM_pos)
    have heta_factor_nonneg :
        0 ≤ Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) :=
      le_of_lt (Real.rpow_pos_of_pos heta_pos ((w - (k : ℝ)) / (k : ℝ)))
    have hconstant :
        (1 / 50 : ℝ) ≤ 1 / ((16 : ℝ) * Real.exp 1) := by
      have hexp_lt_three : Real.exp 1 < 3 := Real.exp_one_lt_three
      have hden_pos : (0 : ℝ) < (16 : ℝ) * Real.exp 1 := by positivity
      have hden_le_fifty : (16 : ℝ) * Real.exp 1 ≤ 50 := by
        nlinarith
      exact one_div_le_one_div_of_le hden_pos hden_le_fifty
    have hmain_term_le :
        (1 / 50 : ℝ) * (k : ℝ) *
            Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) ≤ p * M := by
      rw [hpM_eq]
      have hkR_nonneg : 0 ≤ (k : ℝ) := le_of_lt hkR_pos
      have hcoef_le :
          (1 / 50 : ℝ) * (k : ℝ) ≤
            (k : ℝ) / ((16 : ℝ) * Real.exp 1) := by
        calc
          (1 / 50 : ℝ) * (k : ℝ)
              ≤ (1 / ((16 : ℝ) * Real.exp 1)) * (k : ℝ) := by
                exact mul_le_mul_of_nonneg_right hconstant hkR_nonneg
          _ = (k : ℝ) / ((16 : ℝ) * Real.exp 1) := by ring
      exact mul_le_mul_of_nonneg_right hcoef_le heta_factor_nonneg
    have hsampling_M' :
        p * M - 1 < (RamseyNumber s k : ℝ) := by
      simpa [M] using hsampling_M
    calc
      (1 / 50 : ℝ) * (k : ℝ) *
            Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) - 1
          ≤ p * M - 1 := by linarith
      _ ≤ (RamseyNumber s k : ℝ) := le_of_lt hsampling_M'
  · intro hkRange
    sorry
