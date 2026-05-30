import Tablet.ComplementPolarityPairHsFree
import Tablet.LoopGraphComplementNdLambda
import Tablet.MainTheoremEtaBounds
import Tablet.MainTheoremDyadicGaloisScale
import Tablet.MainTheoremFiniteAbsorption
import Tablet.MainTheoremLargeKComparison
import Tablet.MainTheoremPolarityParameterBounds
import Tablet.MainTheoremPolaritySetup
import Tablet.PolarityGraphParameters
import Tablet.RamseyFromGraphPair

set_option maxHeartbeats 800000

-- [TABLET NODE: MainTheorem]

theorem MainTheorem :
    ∀ s : ℕ, 4 ≤ s → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      c * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  intro s hs
  have hlarge :
      ∃ k0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k0 ≤ k → 2 ≤ k →
        C * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤
          (RamseyNumber s k : ℝ) := by
    classical
    rcases MainTheoremDyadicGaloisScale s hs with
      ⟨kScale, A, B, M, hA_pos, hB_pos, hM_pos, hA_ge_one, hB_ge_one,
        hA_large, hS_le_M, hBpowS_le_M, hBpow200_le_M, hScale⟩
    let Ccmp : ℝ := (B ^ (s - 3))⁻¹
    have hCcmp_pos : 0 < Ccmp := by
      dsimp [Ccmp]
      positivity
    refine ⟨kScale, Ccmp / 200, by positivity, ?_⟩
    intro k hkScale hk2
    rcases hScale k hkScale with
      ⟨m, hm, hcard, hq_lower, hq_upper, hlogq_le_logk, hlogq_pos, hlogk_one,
        hgrowth⟩
    let K := GaloisField 2 m
    let t := s - 2
    let q := 2 ^ m
    let n := (q ^ (t + 1) - 1) / (q - 1)
    let dG := (q ^ t - 1) / (q - 1)
    let dF := n - dG
    let a := (q ^ (t - 1) - 1) / (q - 1)
    let lambda := Real.sqrt (((dG - a : ℕ) : ℝ))
    let Q : ℝ := ((q ^ (t - 1) : ℕ) : ℝ)
    let eta : ℝ :=
      max (lambda ^ 2 / (dG : ℝ) ^ 2)
        (lambda * lambda / ((dF : ℝ) * (dG : ℝ)))
    haveI : Fintype K := Fintype.ofFinite _
    haveI :
        Fintype (Projectivization K (Fin ((s - 2) + 1) → K)) :=
      Fintype.ofFinite _
    have hq_card : q = Fintype.card K := by
      dsimp [K, q]
      rw [Fintype.card_eq_nat_card]
      exact hcard.symm
    have hsetup :
        LoopGraphNdLambda (PolarityGraph K t) n dG lambda ∧
          LoopGraphNdLambda (LoopGraphComplement (PolarityGraph K t)) n dF lambda ∧
            HsFreePair (LoopGraphComplement (PolarityGraph K t))
              (PolarityGraph K t) s := by
      simpa [K, t, q, n, dG, dF, lambda] using
        MainTheoremPolaritySetup K s q hs hq_card
    rcases hsetup with ⟨hG, hF, hFG⟩
    have hparams := MainTheoremPolarityParameterBounds s m hs hm
    have hparams' :
        0 < n ∧ 0 < dF ∧ 0 < dG ∧
          q ^ t ≤ n ∧ n ≤ (t + 1) * q ^ t ∧
          q ^ (t - 1) ≤ dG ∧ dG ≤ t * q ^ (t - 1) ∧
          dF = q ^ t ∧ (dG - a : ℕ) = q ^ (t - 1) ∧
          lambda ^ 2 = Q ∧
          0 < Q ∧
          1 / (n : ℝ) ^ 2 ≤ lambda ^ 2 / (dG : ℝ) ^ 2 ∧
          lambda ^ 2 / (dG : ℝ) ^ 2 ≤ 1 ∧
          lambda * lambda / ((dF : ℝ) * (dG : ℝ)) ≤ 1 ∧
          max (lambda ^ 2 / (dG : ℝ) ^ 2)
            (lambda * lambda / ((dF : ℝ) * (dG : ℝ))) ≤ 1 / Q := by
      simpa only [t, q, n, dG, dF, a, lambda, Q] using hparams
    rcases hparams' with
      ⟨hn_pos, hdF_pos, hdG_pos, hn_lower, hn_upper, hdG_lower, hdG_upper,
        hdF_eq, hdiff_eq, hlambda_sq, hQ_pos, hfirst_lower, hfirst_upper,
        hsecond_upper, heta_upper_Q⟩
    have heta_def :
        eta =
          max (lambda ^ 2 / (dG : ℝ) ^ 2)
            (lambda * lambda / ((dF : ℝ) * (dG : ℝ))) := rfl
    have heta_basic :
        0 < eta ∧ 1 / (n : ℝ) ^ 2 ≤ eta ∧ eta ≤ 1 :=
      MainTheoremEtaBounds n dF dG lambda lambda eta
        hn_pos hdF_pos hdG_pos heta_def hfirst_lower hfirst_upper hsecond_upper
    rcases heta_basic with ⟨heta_pos, heta_lower, heta_upper_one⟩
    have hs3 : 3 ≤ s := by omega
    have hn3 : 3 ≤ n := by
      have ht_ge_two : 2 ≤ t := by
        dsimp [t]
        omega
      have hq_ge_two : 2 ≤ q := by
        dsimp [q]
        exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hm
      have hfour_le_qt : 4 ≤ q ^ t := by
        have hpow : (2 : ℕ) ^ 2 ≤ q ^ t :=
          pow_le_pow hq_ge_two (by omega : 1 ≤ q) ht_ge_two
        norm_num at hpow ⊢
        exact hpow
      omega
    have hk1 : 1 ≤ k := by omega
    let w : ℝ := 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ)
    have hw_def : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ) := rfl
    have hramsey :=
      (RamseyFromGraphPair
        (LoopGraphComplement (PolarityGraph K t)) (PolarityGraph K t)
        s n dF dG k lambda lambda eta w hs3 hn3 hdG_pos hk1
        hF hG hFG heta_def hw_def heta_lower heta_upper_one).2
    let S : ℝ := ((s + 1 : ℕ) : ℝ)
    have hS_ge_one : (1 : ℝ) ≤ S := by
      dsimp [S]
      exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
    have hS_nonneg : (0 : ℝ) ≤ S := le_trans (by norm_num) hS_ge_one
    have hlog_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le zero_lt_one hlogk_one
    have hlog_sq_ge_one : (1 : ℝ) ≤ (Real.log (k : ℝ)) ^ 2 := by
      nlinarith [sq_nonneg (Real.log (k : ℝ) - 1)]
    have hAlog_sq_ge_one : (1 : ℝ) ≤ A * (Real.log (k : ℝ)) ^ 2 := by
      nlinarith [mul_le_mul hA_ge_one hlog_sq_ge_one (by norm_num : (0 : ℝ) ≤ 1)
        (le_of_lt hA_pos)]
    have hq_le_k : (q : ℝ) ≤ (k : ℝ) := by
      have hden_pos : 0 < A * (Real.log (k : ℝ)) ^ 2 := by positivity
      have hx_le_k : (k : ℝ) / (A * (Real.log (k : ℝ)) ^ 2) ≤ (k : ℝ) := by
        rw [div_le_iff₀ hden_pos]
        have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) := by positivity
        nlinarith [hk_nonneg, hAlog_sq_ge_one]
      exact hq_upper.trans hx_le_k
    have hlog_high_ge_one : (1 : ℝ) ≤ (Real.log (k : ℝ)) ^ (2 * s + 2) :=
      one_le_pow₀ hlogk_one
    have hM_le_k : M ≤ (k : ℝ) := by
      calc
        M = M * 1 := by ring
        _ ≤ M * (Real.log (k : ℝ)) ^ (2 * s + 2) :=
          mul_le_mul_of_nonneg_left hlog_high_ge_one (le_of_lt hM_pos)
        _ ≤ (k : ℝ) := hgrowth
    have hS_le_k : S ≤ (k : ℝ) := hS_le_M.trans hM_le_k
    have hlogn_le :
        Real.log (n : ℝ) ≤ S * Real.log (k : ℝ) := by
      have ht1_le_s1_nat : t + 1 ≤ s + 1 := by
        dsimp [t]
        omega
      have ht1_le_S : ((t + 1 : ℕ) : ℝ) ≤ S := by
        dsimp [S]
        exact_mod_cast ht1_le_s1_nat
      have hq_pow_le_k_pow : (q : ℝ) ^ t ≤ (k : ℝ) ^ t :=
        pow_le_pow_left₀ (by positivity) hq_le_k t
      have hn_le_S_kpow : (n : ℝ) ≤ S * (k : ℝ) ^ t := by
        have hn_upper_real : (n : ℝ) ≤ ((t + 1 : ℕ) : ℝ) * (q : ℝ) ^ t := by
          exact_mod_cast hn_upper
        calc
          (n : ℝ) ≤ ((t + 1 : ℕ) : ℝ) * (q : ℝ) ^ t := hn_upper_real
          _ ≤ S * (k : ℝ) ^ t :=
            mul_le_mul ht1_le_S hq_pow_le_k_pow (by positivity) (by positivity)
      have hS_kpow_le_kpow_succ : S * (k : ℝ) ^ t ≤ (k : ℝ) ^ (t + 1) := by
        calc
          S * (k : ℝ) ^ t ≤ (k : ℝ) * (k : ℝ) ^ t :=
            mul_le_mul_of_nonneg_right hS_le_k (by positivity)
          _ = (k : ℝ) ^ (t + 1) := by
            rw [pow_succ]
            ring
      have hn_le_kpow : (n : ℝ) ≤ (k : ℝ) ^ (t + 1) :=
        hn_le_S_kpow.trans hS_kpow_le_kpow_succ
      have hkpow_pos : 0 < (k : ℝ) ^ (t + 1) := by positivity
      have hlog_le_pow : Real.log (n : ℝ) ≤ Real.log ((k : ℝ) ^ (t + 1)) :=
        Real.log_le_log (by exact_mod_cast hn_pos) hn_le_kpow
      calc
        Real.log (n : ℝ) ≤ Real.log ((k : ℝ) ^ (t + 1)) := hlog_le_pow
        _ = ((t + 1 : ℕ) : ℝ) * Real.log (k : ℝ) := by
          rw [Real.log_pow]
        _ ≤ S * Real.log (k : ℝ) :=
          mul_le_mul_of_nonneg_right ht1_le_S (le_of_lt hlog_pos)
    have hRangeUpper : (k : ℝ) ≤ eta * (dF : ℝ) * (n : ℝ) := by
      have ht_ge_two : 2 ≤ t := by
        dsimp [t]
        omega
      have ht_pos : (0 : ℝ) < (t : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) ht_ge_two)
      have hdFR_pos : (0 : ℝ) < dF := by exact_mod_cast hdF_pos
      have hdGR_pos : (0 : ℝ) < dG := by exact_mod_cast hdG_pos
      have ht_le_S : (t : ℝ) ≤ S := by
        dsimp [t, S]
        exact_mod_cast (by omega : s - 2 ≤ s + 1)
      have hS_le_sq : S ≤ S ^ 2 := by
        have hmul : S * (1 : ℝ) ≤ S * S :=
          mul_le_mul_of_nonneg_left hS_ge_one hS_nonneg
        simpa [pow_two] using hmul
      have hBpow_t_le : B ^ t ≤ B ^ (s + 1) :=
        pow_le_pow_right₀ hB_ge_one (by dsimp [t]; omega)
      have hcoef_le_M : (t : ℝ) * B ^ t ≤ M := by
        calc
          (t : ℝ) * B ^ t ≤ S * B ^ (s + 1) := by
            exact mul_le_mul ht_le_S hBpow_t_le (by positivity) hS_nonneg
          _ ≤ S ^ 2 * B ^ (s + 1) :=
            mul_le_mul_of_nonneg_right hS_le_sq (by positivity)
          _ = B ^ (s + 1) * S ^ 2 := by ring
          _ ≤ M := hBpowS_le_M
      have hlog_pow_le :
          (Real.log (k : ℝ)) ^ (2 * t) ≤
            (Real.log (k : ℝ)) ^ (2 * s + 2) :=
        pow_le_pow_right₀ hlogk_one (by dsimp [t]; omega)
      have hcoef_log_le_k :
          (t : ℝ) * B ^ t * (Real.log (k : ℝ)) ^ (2 * t) ≤ (k : ℝ) := by
        calc
          (t : ℝ) * B ^ t * (Real.log (k : ℝ)) ^ (2 * t)
              ≤ M * (Real.log (k : ℝ)) ^ (2 * s + 2) :=
                mul_le_mul hcoef_le_M hlog_pow_le (by positivity) (le_of_lt hM_pos)
          _ ≤ (k : ℝ) := hgrowth
      have hden_pow :
          (B * (Real.log (k : ℝ)) ^ 2) ^ t =
            B ^ t * (Real.log (k : ℝ)) ^ (2 * t) := by
        rw [mul_pow, pow_mul]
      have hden_pow_main :
          ((t : ℝ) * (k : ℝ)) * (B * (Real.log (k : ℝ)) ^ 2) ^ t ≤
            (k : ℝ) ^ t := by
        calc
          ((t : ℝ) * (k : ℝ)) * (B * (Real.log (k : ℝ)) ^ 2) ^ t
              = ((t : ℝ) * B ^ t * (Real.log (k : ℝ)) ^ (2 * t)) *
                (k : ℝ) := by
                rw [hden_pow]
                ring
          _ ≤ (k : ℝ) * (k : ℝ) :=
                mul_le_mul hcoef_log_le_k (le_refl (k : ℝ)) (by positivity) (by positivity)
          _ = (k : ℝ) ^ 2 := by ring
          _ ≤ (k : ℝ) ^ t :=
                pow_le_pow_right₀ (by exact_mod_cast hk1 : (1 : ℝ) ≤ k) ht_ge_two
      have hbase_nonneg :
          0 ≤ (k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2) := by positivity
      have hqpow_lower :
          ((k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2)) ^ t ≤ (q : ℝ) ^ t :=
        pow_le_pow_left₀ hbase_nonneg hq_lower t
      have hk_le_base_pow_div_t :
          (k : ℝ) ≤
            ((k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2)) ^ t / (t : ℝ) := by
        have hden_pos : 0 < B * (Real.log (k : ℝ)) ^ 2 := by positivity
        have hdenpow_pos : 0 < (B * (Real.log (k : ℝ)) ^ 2) ^ t := by
          positivity
        rw [le_div_iff₀ ht_pos]
        rw [div_pow]
        rw [le_div_iff₀ hdenpow_pos]
        simpa [mul_assoc, mul_comm, mul_left_comm] using hden_pow_main
      have hk_le_qt_div_t : (k : ℝ) ≤ (q : ℝ) ^ t / (t : ℝ) := by
        exact hk_le_base_pow_div_t.trans
          (div_le_div_of_nonneg_right hqpow_lower (le_of_lt ht_pos))
      have hQ_le_eta : Q / ((dF : ℝ) * (dG : ℝ)) ≤ eta := by
        have hsecond_le :
            lambda * lambda / ((dF : ℝ) * (dG : ℝ)) ≤ eta := by
          dsimp [eta]
          exact le_max_right _ _
        have hsecond_eq :
            lambda * lambda / ((dF : ℝ) * (dG : ℝ)) =
              Q / ((dF : ℝ) * (dG : ℝ)) := by
          calc
            lambda * lambda / ((dF : ℝ) * (dG : ℝ))
                = lambda ^ 2 / ((dF : ℝ) * (dG : ℝ)) := by ring
            _ = Q / ((dF : ℝ) * (dG : ℝ)) := by rw [hlambda_sq]
        simpa [hsecond_eq] using hsecond_le
      have hn_lower_real : (q : ℝ) ^ t ≤ (n : ℝ) := by
        exact_mod_cast hn_lower
      have hdG_upper_real : (dG : ℝ) ≤ (t : ℝ) * Q := by
        dsimp [Q]
        exact_mod_cast hdG_upper
      have hqt_div_t_le_Qn_div_dG :
          (q : ℝ) ^ t / (t : ℝ) ≤ Q * (n : ℝ) / (dG : ℝ) := by
        rw [div_le_div_iff₀ ht_pos hdGR_pos]
        calc
          (q : ℝ) ^ t * (dG : ℝ)
              ≤ (q : ℝ) ^ t * ((t : ℝ) * Q) :=
                mul_le_mul_of_nonneg_left hdG_upper_real (by positivity)
          _ = ((t : ℝ) * Q) * (q : ℝ) ^ t := by ring
          _ ≤ ((t : ℝ) * Q) * (n : ℝ) :=
                mul_le_mul_of_nonneg_left hn_lower_real (by positivity)
          _ = Q * (n : ℝ) * (t : ℝ) := by ring_nf
      have hQn_eq :
          Q * (n : ℝ) / (dG : ℝ) =
            (Q / ((dF : ℝ) * (dG : ℝ))) * (dF : ℝ) * (n : ℝ) := by
        field_simp [ne_of_gt hdFR_pos, ne_of_gt hdGR_pos]
      have hprod_le :
          (Q / ((dF : ℝ) * (dG : ℝ))) * (dF : ℝ) * (n : ℝ) ≤
            eta * (dF : ℝ) * (n : ℝ) := by
        have h1 :
            (Q / ((dF : ℝ) * (dG : ℝ))) * (dF : ℝ) ≤ eta * (dF : ℝ) :=
          mul_le_mul_of_nonneg_right hQ_le_eta (le_of_lt hdFR_pos)
        exact mul_le_mul_of_nonneg_right h1 (by positivity)
      calc
        (k : ℝ) ≤ (q : ℝ) ^ t / (t : ℝ) := hk_le_qt_div_t
        _ ≤ Q * (n : ℝ) / (dG : ℝ) := hqt_div_t_le_Qn_div_dG
        _ = (Q / ((dF : ℝ) * (dG : ℝ))) * (dF : ℝ) * (n : ℝ) := hQn_eq
        _ ≤ eta * (dF : ℝ) * (n : ℝ) := hprod_le
    have hRangeLower :
        (100 : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 / (dG : ℝ) ≤
          (k : ℝ) := by
      have hdGR_pos : (0 : ℝ) < dG := by exact_mod_cast hdG_pos
      rw [div_le_iff₀ hdGR_pos]
      have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n))
      have hSlog_nonneg : 0 ≤ S * Real.log (k : ℝ) := by positivity
      have hlogn_sq_le :
          (Real.log (n : ℝ)) ^ 2 ≤ (S * Real.log (k : ℝ)) ^ 2 := by
        simpa [pow_two] using
          mul_le_mul hlogn_le hlogn_le hlogn_nonneg hSlog_nonneg
      have ht1_le_s1_nat : t + 1 ≤ s + 1 := by
        dsimp [t]
        omega
      have ht1_le_S : ((t + 1 : ℕ) : ℝ) ≤ S := by
        dsimp [S]
        exact_mod_cast ht1_le_s1_nat
      have hcoef_le_A :
          (100 : ℝ) * ((t + 1 : ℕ) : ℝ) * S ^ 2 ≤ A := by
        calc
          (100 : ℝ) * ((t + 1 : ℕ) : ℝ) * S ^ 2
              ≤ (100 : ℝ) * S * S ^ 2 := by
                gcongr
          _ = (100 : ℝ) * S ^ 3 := by ring
          _ ≤ A := hA_large
      have hAqlog_le_k :
          A * (q : ℝ) * (Real.log (k : ℝ)) ^ 2 ≤ (k : ℝ) := by
        have hden_pos : 0 < A * (Real.log (k : ℝ)) ^ 2 := by positivity
        have hq_upper' := hq_upper
        rw [le_div_iff₀ hden_pos] at hq_upper'
        nlinarith
      have hn_upper_real :
          (n : ℝ) ≤ ((t + 1 : ℕ) : ℝ) * (q : ℝ) ^ t := by
        exact_mod_cast hn_upper
      have hdG_lower_real : (q : ℝ) ^ (t - 1) ≤ (dG : ℝ) := by
        exact_mod_cast hdG_lower
      have ht_eq : t = (t - 1) + 1 := by
        dsimp [t]
        omega
      have hqt_decomp : (q : ℝ) ^ t = (q : ℝ) ^ (t - 1) * (q : ℝ) := by
        calc
          (q : ℝ) ^ t = (q : ℝ) ^ ((t - 1) + 1) :=
            congrArg (fun u : ℕ => (q : ℝ) ^ u) ht_eq
          _ = (q : ℝ) ^ (t - 1) * (q : ℝ) := by rw [pow_succ]
      have hleft_le :
          (100 : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ 2 ≤
            (A * (q : ℝ) * (Real.log (k : ℝ)) ^ 2) * (q : ℝ) ^ (t - 1) := by
        calc
          (100 : ℝ) * (n : ℝ) * (Real.log (n : ℝ)) ^ 2
              ≤ (100 : ℝ) * (((t + 1 : ℕ) : ℝ) * (q : ℝ) ^ t) *
                  (S * Real.log (k : ℝ)) ^ 2 := by
                gcongr
          _ = ((100 : ℝ) * ((t + 1 : ℕ) : ℝ) * S ^ 2) *
                ((q : ℝ) ^ (t - 1) * ((q : ℝ) * (Real.log (k : ℝ)) ^ 2)) := by
                rw [hqt_decomp]
                ring
          _ ≤ A * ((q : ℝ) ^ (t - 1) * ((q : ℝ) * (Real.log (k : ℝ)) ^ 2)) := by
                exact mul_le_mul_of_nonneg_right hcoef_le_A (by positivity)
          _ = (A * (q : ℝ) * (Real.log (k : ℝ)) ^ 2) * (q : ℝ) ^ (t - 1) := by
                ring
      have hright_le :
          (A * (q : ℝ) * (Real.log (k : ℝ)) ^ 2) * (q : ℝ) ^ (t - 1) ≤
            (k : ℝ) * (dG : ℝ) := by
        exact mul_le_mul hAqlog_le_k hdG_lower_real (by positivity) (by positivity)
      exact hleft_le.trans hright_le
    have hramsey_lower :
        (k : ℝ) / (100 * eta) - 1 ≤ (RamseyNumber s k : ℝ) :=
      hramsey ⟨hRangeUpper, hRangeLower⟩
    have heta_upper_for_comparison : eta ≤ 1 / Q := by
      simpa only [eta] using heta_upper_Q
    have hQ_lower :
        Ccmp * ((k : ℝ) ^ (s - 3)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤ Q := by
      have hlog_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le zero_lt_one hlogk_one
      have hbase_nonneg :
          0 ≤ (k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2) := by
        positivity
      have hpow_lower :
          ((k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2)) ^ (s - 3) ≤
            (q : ℝ) ^ (s - 3) :=
        pow_le_pow_left₀ hbase_nonneg hq_lower (s - 3)
      have hleft_eq :
          Ccmp * ((k : ℝ) ^ (s - 3)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) =
            ((k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2)) ^ (s - 3) := by
        dsimp [Ccmp]
        have htwo_mul : 2 * s - 6 = 2 * (s - 3) := by omega
        rw [htwo_mul]
        field_simp [ne_of_gt hB_pos, ne_of_gt hlog_pos]
        rw [pow_mul (Real.log (k : ℝ)) 2 (s - 3)]
        rw [← mul_pow B ((Real.log (k : ℝ)) ^ 2) (s - 3)]
        rw [← mul_pow (B * (Real.log (k : ℝ)) ^ 2)
          ((k : ℝ) / (B * Real.log (k : ℝ) ^ 2)) (s - 3)]
        have hbase :
            (B * Real.log (k : ℝ) ^ 2) *
                ((k : ℝ) / (B * Real.log (k : ℝ) ^ 2)) = (k : ℝ) := by
          field_simp [ne_of_gt hB_pos, ne_of_gt hlog_pos]
        rw [hbase]
      have hQ_eq : (q : ℝ) ^ (s - 3) = Q := by
        have ht_sub : t - 1 = s - 3 := by
          dsimp [t]
          omega
        dsimp [Q]
        rw [ht_sub]
        norm_num
      calc
        Ccmp * ((k : ℝ) ^ (s - 3)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))
            = ((k : ℝ) / (B * (Real.log (k : ℝ)) ^ 2)) ^ (s - 3) := hleft_eq
        _ ≤ (q : ℝ) ^ (s - 3) := hpow_lower
        _ = Q := hQ_eq
    have habsorb :
        1 ≤ (Ccmp / (200 * 1)) *
          (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))) := by
      have hlog_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le zero_lt_one hlogk_one
      have hlog_pow_le :
          (Real.log (k : ℝ)) ^ (2 * s - 6) ≤
            (Real.log (k : ℝ)) ^ (2 * s + 2) :=
        pow_le_pow_right₀ hlogk_one (by omega : 2 * s - 6 ≤ 2 * s + 2)
      have hBpow_le : B ^ (s - 3) ≤ B ^ (s + 1) :=
        pow_le_pow_right₀ hB_ge_one (by omega : s - 3 ≤ s + 1)
      have hcoef_le_M : (200 : ℝ) * B ^ (s - 3) ≤ M :=
        (mul_le_mul_of_nonneg_left hBpow_le (by norm_num)).trans hBpow200_le_M
      have hcoef_nonneg : (0 : ℝ) ≤ (200 : ℝ) * B ^ (s - 3) := by positivity
      have hden_le_k :
          (200 : ℝ) * B ^ (s - 3) * (Real.log (k : ℝ)) ^ (2 * s - 6) ≤
            (k : ℝ) := by
        calc
          (200 : ℝ) * B ^ (s - 3) * (Real.log (k : ℝ)) ^ (2 * s - 6)
              ≤ M * (Real.log (k : ℝ)) ^ (2 * s + 2) := by
                exact mul_le_mul hcoef_le_M hlog_pow_le (by positivity) (le_of_lt hM_pos)
          _ ≤ (k : ℝ) := hgrowth
      have hk_ge_one : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
      have hk_le_pow : (k : ℝ) ≤ (k : ℝ) ^ (s - 2) := by
        have hpow : (k : ℝ) ^ 1 ≤ (k : ℝ) ^ (s - 2) :=
          pow_le_pow_right₀ hk_ge_one (by omega : 1 ≤ s - 2)
        simpa using hpow
      have hden_le_kpow :
          (200 : ℝ) * B ^ (s - 3) * (Real.log (k : ℝ)) ^ (2 * s - 6) ≤
            (k : ℝ) ^ (s - 2) :=
        hden_le_k.trans hk_le_pow
      have hden_pos :
          0 < (200 : ℝ) * B ^ (s - 3) * (Real.log (k : ℝ)) ^ (2 * s - 6) := by
        positivity
      have htarget_eq :
          (Ccmp / (200 * 1)) *
              (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))) =
            ((k : ℝ) ^ (s - 2)) /
              ((200 : ℝ) * B ^ (s - 3) * (Real.log (k : ℝ)) ^ (2 * s - 6)) := by
        dsimp [Ccmp]
        field_simp [ne_of_gt hB_pos, ne_of_gt hlog_pos]
      rw [htarget_eq]
      rw [le_div_iff₀ hden_pos]
      simpa using hden_le_kpow
    have hcomparison :
        (Ccmp / (200 * 1)) *
            (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))) ≤
          (k : ℝ) / (100 * eta) - 1 :=
      MainTheoremLargeKComparison s k Ccmp 1 Q eta hs hk2 (by norm_num)
        hQ_pos heta_pos heta_upper_for_comparison hQ_lower habsorb
    calc
      (Ccmp / 200) * ((k : ℝ) ^ (s - 2)) /
          ((Real.log (k : ℝ)) ^ (2 * s - 6))
          = (Ccmp / (200 * 1)) *
              (((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))) := by
            ring
      _ ≤ (k : ℝ) / (100 * eta) - 1 := hcomparison
      _ ≤ (RamseyNumber s k : ℝ) := hramsey_lower
  rcases hlarge with ⟨k0, C, hC, hlarge_bound⟩
  exact MainTheoremFiniteAbsorption s k0 C hs hC hlarge_bound
