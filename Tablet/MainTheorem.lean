import Tablet.DigraphToGraphIndependentSetBound
import Tablet.MainTheoremDyadicFieldScale
import Tablet.MainTheoremLinearLogSqGrowth
import Tablet.MainTheoremLogSquaredPowerBound
import Tablet.MainTheoremRamseyPositive
import Tablet.MainTheoremSamplingBridge
import Tablet.PolarityGraphParameters
import Tablet.ProductDigraphVertexCard
import Tablet.RamseyNumber
import Tablet.SamplingKsFreeRamseyBound
import Tablet.StarProductDigraph
import Tablet.StarProductDigraphTransitiveFree
import Tablet.StarProductForwardIndependentBound

set_option maxHeartbeats 800000

-- [TABLET NODE: MainTheorem]

theorem MainTheorem :
    ∀ s : ℕ, 3 ≤ s → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      c * ((k : ℝ) ^ (s - 1)) / ((Real.log (k : ℝ)) ^ (2 * s - 4)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  classical
  intro s hs
  let t : ℕ := s - 1
  have ht : 2 ≤ t := by
    dsimp [t]
    omega
  have ht_pos : 0 < t := by omega
  have ht_succ : t + 1 = s := by
    dsimp [t]
    omega
  have hs_t : s - 1 = t := rfl
  have hexp_t : 2 * s - 4 = 2 * (t - 1) := by
    dsimp [t]
    omega
  rcases MainTheoremSamplingBridge t ht with ⟨C, hC, hbridge⟩
  rcases MainTheoremDyadicFieldScale C hC with ⟨cD, hcD, XD, hdyadic⟩
  rcases MainTheoremLogSquaredPowerBound with ⟨Q0, hlogsq_power⟩
  let Bq : ℝ := max Q0 1
  have hBq_pos : 0 < Bq := by
    dsimp [Bq]
    exact lt_of_lt_of_le zero_lt_one (le_max_right Q0 1)
  rcases MainTheoremLinearLogSqGrowth cD Bq hcD hBq_pos with
    ⟨Xq, hq_growth⟩
  let cLarge : ℝ := cD ^ (t - 1) / (8 * Real.exp 1 * C)
  have hcLarge_pos : 0 < cLarge := by
    dsimp [cLarge]
    positivity
  let Y : ℝ := max (max (max XD Xq) (8 * Real.exp 1 * C)) 2
  have hY_ge_XD : XD ≤ Y := by
    dsimp [Y]
    exact (le_max_left XD Xq).trans
      ((le_max_left (max XD Xq) (8 * Real.exp 1 * C)).trans
        (le_max_left (max (max XD Xq) (8 * Real.exp 1 * C)) 2))
  have hY_ge_Xq : Xq ≤ Y := by
    dsimp [Y]
    exact (le_max_right XD Xq).trans
      ((le_max_left (max XD Xq) (8 * Real.exp 1 * C)).trans
        (le_max_left (max (max XD Xq) (8 * Real.exp 1 * C)) 2))
  have hY_ge_absorb : 8 * Real.exp 1 * C ≤ Y := by
    dsimp [Y]
    exact (le_max_right (max XD Xq) (8 * Real.exp 1 * C)).trans
      (le_max_left (max (max XD Xq) (8 * Real.exp 1 * C)) 2)
  have hY_ge_two : (2 : ℝ) ≤ Y := by
    dsimp [Y]
    exact le_max_right (max (max XD Xq) (8 * Real.exp 1 * C)) 2
  have hY_pos : 0 < Y := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) hY_ge_two
  have hlog2_pos : 0 < Real.log (2 : ℝ) :=
    Real.log_pos (by norm_num : (1 : ℝ) < 2)
  let Bsmall : ℝ :=
    Y ^ (s - 1) / (Real.log (2 : ℝ)) ^ (2 * s - 4) + 1
  have hBsmall_pos : 0 < Bsmall := by
    have hnum_nonneg : 0 ≤ Y ^ (s - 1) := pow_nonneg hY_pos.le _
    have hden_pos : 0 < (Real.log (2 : ℝ)) ^ (2 * s - 4) :=
      pow_pos hlog2_pos _
    have hfrac_nonneg :
        0 ≤ Y ^ (s - 1) / (Real.log (2 : ℝ)) ^ (2 * s - 4) :=
      div_nonneg hnum_nonneg hden_pos.le
    dsimp [Bsmall]
    linarith
  let c : ℝ := min cLarge (1 / Bsmall)
  have hc_pos : 0 < c := by
    dsimp [c]
    exact lt_min hcLarge_pos (one_div_pos.mpr hBsmall_pos)
  refine ⟨c, hc_pos, ?_⟩
  intro k hk
  have hk_one : 1 ≤ k := by omega
  have hk_pos_nat : 0 < k := by omega
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hkR_nonneg : 0 ≤ (k : ℝ) := le_of_lt hkR_pos
  have hlogk_pos : 0 < Real.log (k : ℝ) := by
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < k))
  have hlogk_nonneg : 0 ≤ Real.log (k : ℝ) := le_of_lt hlogk_pos
  have hden_target_pos :
      0 < (Real.log (k : ℝ)) ^ (2 * s - 4) := pow_pos hlogk_pos _
  have htarget_nonneg :
      0 ≤ ((k : ℝ) ^ (s - 1)) /
          ((Real.log (k : ℝ)) ^ (2 * s - 4)) := by
    exact div_nonneg (pow_nonneg hkR_nonneg _) hden_target_pos.le
  by_cases hlarge : Y ≤ (k : ℝ)
  · have hXDk : XD ≤ (k : ℝ) := hY_ge_XD.trans hlarge
    have hXqk : Xq ≤ (k : ℝ) := hY_ge_Xq.trans hlarge
    have hk_absorb : 8 * Real.exp 1 * C ≤ (k : ℝ) :=
      hY_ge_absorb.trans hlarge
    rcases hdyadic k hXDk with
      ⟨m, hm_pos, hcard, hk_scale_lower, hk_scale_upper, hCq,
        hq_four, hlogq_le_logk, hq_lower⟩
    let q : ℕ := 2 ^ m
    let K : Type := GaloisField 2 m
    haveI : Fintype K := Fintype.ofFinite K
    haveI :
        Fintype (Projectivization K (Fin (t + 1) → K)) :=
      Fintype.ofFinite _
    haveI : Fintype (ProductDigraphVertex (PolarityGraph K t)) :=
      Fintype.ofFinite _
    have hm_ne : m ≠ 0 := by omega
    have hq_card : q = Fintype.card K := by
      dsimp [K, q]
      rw [Fintype.card_eq_nat_card]
      exact hcard.symm
    have hq_pos_nat : 0 < q := by
      dsimp [q]
      positivity
    have hqR_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
    have hqR_nonneg : 0 ≤ (q : ℝ) := le_of_lt hqR_pos
    have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ q)
    have hBq_le_scale :
        Bq ≤ cD * (k : ℝ) / (Real.log (k : ℝ)) ^ 2 :=
      hq_growth k hXqk
    have hQ0_le_q : Q0 ≤ (q : ℝ) := by
      exact (le_max_left Q0 1).trans (hBq_le_scale.trans hq_lower)
    have hlogsq_bound :
        4 * (Real.log (q : ℝ)) ^ 2 ≤ Real.exp 1 * (q : ℝ) :=
      hlogsq_power q hQ0_le_q
    have hq_sq_le_qt : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ t :=
      pow_le_pow_right₀ hq_ge_one (by omega : 2 ≤ t)
    have hbridge_side :
        (k : ℝ) ≤ Real.exp 1 * C * (q : ℝ) ^ t := by
      calc
        (k : ℝ) ≤ 4 * C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 :=
          hk_scale_upper
        _ = C * (q : ℝ) * (4 * (Real.log (q : ℝ)) ^ 2) := by ring
        _ ≤ C * (q : ℝ) * (Real.exp 1 * (q : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hlogsq_bound (by positivity)
        _ = Real.exp 1 * C * (q : ℝ) ^ 2 := by ring
        _ ≤ Real.exp 1 * C * (q : ℝ) ^ t := by
          exact mul_le_mul_of_nonneg_left hq_sq_le_qt (by positivity)
    have hbridge_result :
        (k : ℝ) * (q : ℝ) ^ (t - 1) /
              (4 * Real.exp 1 * C) - 1 <
            (RamseyNumber (t + 1) k : ℝ) :=
      hbridge K q hq_card k hk_one hCq hk_scale_lower hbridge_side
    have hbridge_s :
        (k : ℝ) * (q : ℝ) ^ (t - 1) /
              (4 * Real.exp 1 * C) - 1 <
            (RamseyNumber s k : ℝ) := by
      simpa [ht_succ] using hbridge_result
    let n : ℕ := t - 1
    have ht_eq_n_succ : t = n + 1 := by
      dsimp [n]
      omega
    let L : ℝ := (Real.log (k : ℝ)) ^ 2
    have hL_pos : 0 < L := by
      dsimp [L]
      exact sq_pos_of_ne_zero hlogk_pos.ne'
    have hL_nonneg : 0 ≤ L := le_of_lt hL_pos
    have hbase_nonneg : 0 ≤ cD * (k : ℝ) / L := by
      dsimp [L]
      positivity
    have hq_lower_L : cD * (k : ℝ) / L ≤ (q : ℝ) := by
      simpa [L, q] using hq_lower
    have hqpow_lower :
        (cD * (k : ℝ) / L) ^ n ≤ (q : ℝ) ^ n :=
      pow_le_pow_left₀ hbase_nonneg hq_lower_L n
    have htarget_rewrite :
        ((k : ℝ) ^ (s - 1)) /
            ((Real.log (k : ℝ)) ^ (2 * s - 4)) =
          (k : ℝ) ^ t / L ^ n := by
      dsimp [L, n]
      rw [hs_t, hexp_t, pow_mul]
    have hlarge_factor :
        cLarge * ((k : ℝ) ^ t / L ^ n) =
          (k : ℝ) * (cD * (k : ℝ) / L) ^ n /
            (8 * Real.exp 1 * C) := by
      dsimp [cLarge]
      change cD ^ n / (8 * Real.exp 1 * C) * ((k : ℝ) ^ t / L ^ n) =
        (k : ℝ) * (cD * (k : ℝ) / L) ^ n / (8 * Real.exp 1 * C)
      rw [ht_eq_n_succ, pow_succ]
      rw [div_pow, mul_pow]
      field_simp [hL_pos.ne', hC.ne', (Real.exp_pos 1).ne']
    have hden8_pos : 0 < 8 * Real.exp 1 * C := by positivity
    have hlarge_to_half :
        cLarge * (((k : ℝ) ^ (s - 1)) /
            ((Real.log (k : ℝ)) ^ (2 * s - 4))) ≤
          (k : ℝ) * (q : ℝ) ^ n / (8 * Real.exp 1 * C) := by
      rw [htarget_rewrite, hlarge_factor]
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqpow_lower hkR_nonneg) hden8_pos.le
    have hqpow_ge_one : (1 : ℝ) ≤ (q : ℝ) ^ n :=
      one_le_pow₀ hq_ge_one
    have hmain_ge_two :
        (2 : ℝ) ≤ (k : ℝ) * (q : ℝ) ^ n / (4 * Real.exp 1 * C) := by
      have hden4_pos : 0 < 4 * Real.exp 1 * C := by positivity
      rw [le_div_iff₀ hden4_pos]
      have hk_le_kq : (k : ℝ) ≤ (k : ℝ) * (q : ℝ) ^ n := by
        simpa [mul_one] using
          mul_le_mul_of_nonneg_left hqpow_ge_one hkR_nonneg
      calc
        (2 : ℝ) * (4 * Real.exp 1 * C)
            = 8 * Real.exp 1 * C := by ring
        _ ≤ (k : ℝ) := hk_absorb
        _ ≤ (k : ℝ) * (q : ℝ) ^ n := hk_le_kq
    have hhalf_absorb :
        (k : ℝ) * (q : ℝ) ^ n / (8 * Real.exp 1 * C) ≤
          (k : ℝ) * (q : ℝ) ^ n / (4 * Real.exp 1 * C) - 1 := by
      have hhalf :
          (k : ℝ) * (q : ℝ) ^ n / (8 * Real.exp 1 * C) =
            ((k : ℝ) * (q : ℝ) ^ n / (4 * Real.exp 1 * C)) / 2 := by
        field_simp [hC.ne', (Real.exp_pos 1).ne']
        ring
      rw [hhalf]
      linarith
    have hc_le_large : c ≤ cLarge := by
      dsimp [c]
      exact min_le_left _ _
    calc
      c * ((k : ℝ) ^ (s - 1)) /
          ((Real.log (k : ℝ)) ^ (2 * s - 4))
          = c * (((k : ℝ) ^ (s - 1)) /
              ((Real.log (k : ℝ)) ^ (2 * s - 4))) := by ring
      _ ≤ cLarge * (((k : ℝ) ^ (s - 1)) /
              ((Real.log (k : ℝ)) ^ (2 * s - 4))) := by
            exact mul_le_mul_of_nonneg_right hc_le_large htarget_nonneg
      _ ≤ (k : ℝ) * (q : ℝ) ^ n / (8 * Real.exp 1 * C) := hlarge_to_half
      _ ≤ (k : ℝ) * (q : ℝ) ^ n / (4 * Real.exp 1 * C) - 1 := hhalf_absorb
      _ = (k : ℝ) * (q : ℝ) ^ (t - 1) /
            (4 * Real.exp 1 * C) - 1 := by
            dsimp [n]
      _ ≤ (RamseyNumber s k : ℝ) := le_of_lt hbridge_s
  · have hk_lt_Y : (k : ℝ) < Y := lt_of_not_ge hlarge
    have hk_le_Y : (k : ℝ) ≤ Y := le_of_lt hk_lt_Y
    have hlog2_le_logk : Real.log (2 : ℝ) ≤ Real.log (k : ℝ) := by
      exact Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (by exact_mod_cast hk)
    have hden2_pos : 0 < (Real.log (2 : ℝ)) ^ (2 * s - 4) :=
      pow_pos hlog2_pos _
    have hden2_nonneg :
        0 ≤ (Real.log (2 : ℝ)) ^ (2 * s - 4) := le_of_lt hden2_pos
    have hlogpow_mono :
        (Real.log (2 : ℝ)) ^ (2 * s - 4) ≤
          (Real.log (k : ℝ)) ^ (2 * s - 4) :=
      pow_le_pow_left₀ hlog2_pos.le hlog2_le_logk _
    have hnum_mono :
        (k : ℝ) ^ (s - 1) ≤ Y ^ (s - 1) :=
      pow_le_pow_left₀ hkR_nonneg hk_le_Y _
    have hYpow_nonneg : 0 ≤ Y ^ (s - 1) := pow_nonneg hY_pos.le _
    have hsmall_scale_bound :
        ((k : ℝ) ^ (s - 1)) /
            ((Real.log (k : ℝ)) ^ (2 * s - 4)) ≤
          Y ^ (s - 1) / (Real.log (2 : ℝ)) ^ (2 * s - 4) := by
      have hfirst :
          ((k : ℝ) ^ (s - 1)) /
              ((Real.log (k : ℝ)) ^ (2 * s - 4)) ≤
            Y ^ (s - 1) /
              ((Real.log (k : ℝ)) ^ (2 * s - 4)) :=
        div_le_div_of_nonneg_right hnum_mono hden_target_pos.le
      have hsecond :
          Y ^ (s - 1) /
              ((Real.log (k : ℝ)) ^ (2 * s - 4)) ≤
            Y ^ (s - 1) /
              (Real.log (2 : ℝ)) ^ (2 * s - 4) :=
        div_le_div_of_nonneg_left hYpow_nonneg hden2_pos hlogpow_mono
      exact hfirst.trans hsecond
    have hscale_le_Bsmall :
        ((k : ℝ) ^ (s - 1)) /
            ((Real.log (k : ℝ)) ^ (2 * s - 4)) ≤ Bsmall := by
      dsimp [Bsmall]
      linarith
    have hc_le_small : c ≤ 1 / Bsmall := by
      dsimp [c]
      exact min_le_right _ _
    have hramsey_one_nat : 1 ≤ RamseyNumber s k :=
      MainTheoremRamseyPositive s k (by omega) hk_one
    have hramsey_one : (1 : ℝ) ≤ (RamseyNumber s k : ℝ) := by
      exact_mod_cast hramsey_one_nat
    calc
      c * ((k : ℝ) ^ (s - 1)) /
          ((Real.log (k : ℝ)) ^ (2 * s - 4))
          = c * (((k : ℝ) ^ (s - 1)) /
              ((Real.log (k : ℝ)) ^ (2 * s - 4))) := by ring
      _ ≤ (1 / Bsmall) * (((k : ℝ) ^ (s - 1)) /
              ((Real.log (k : ℝ)) ^ (2 * s - 4))) := by
            exact mul_le_mul_of_nonneg_right hc_le_small htarget_nonneg
      _ ≤ (1 / Bsmall) * Bsmall := by
            exact mul_le_mul_of_nonneg_left hscale_le_Bsmall
              (one_div_pos.mpr hBsmall_pos).le
      _ = 1 := by field_simp [hBsmall_pos.ne']
      _ ≤ (RamseyNumber s k : ℝ) := hramsey_one
