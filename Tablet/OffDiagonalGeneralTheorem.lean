import Tablet.ComplementPolarityPairHsFree
import Tablet.MainTheoremEtaBounds
import Tablet.MainTheoremPolarityParameterBounds
import Tablet.MainTheoremPolaritySetup
import Tablet.OffDiagonalGeneralDyadicScale
import Tablet.PolarityGraphParameters
import Tablet.RamseyFromGraphPair

-- [TABLET NODE: OffDiagonalGeneralTheorem]

theorem OffDiagonalGeneralTheorem :
    ∀ delta : ℝ, 0 < delta → ∃ L : ℕ, ∀ s k : ℕ, L ≤ s → L * s ≤ k →
      Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta) * (s : ℝ)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  intro delta hdelta
  let delta0 : ℝ := min (delta / 2) (1 / 20)
  have hdelta0_pos : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min (half_pos hdelta) (by norm_num)
  have hdelta0_le_delta : delta0 ≤ delta := by
    dsimp [delta0]
    exact (min_le_left _ _).trans (by linarith)
  have hdelta0_lt_tenth : delta0 < 1 / 10 := by
    dsimp [delta0]
    have hle : min (delta / 2) (1 / 20 : ℝ) ≤ 1 / 20 := min_le_right _ _
    linarith
  have hnormalized :
      ∃ L0 : ℕ, ∀ s k : ℕ, L0 ≤ s → L0 * s ≤ k →
        Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta0) * (s : ℝ)) ≤
          (RamseyNumber s k : ℝ) := by
    rcases OffDiagonalGeneralDyadicScale delta0 hdelta0_pos hdelta0_lt_tenth with
      ⟨X0, hscale⟩
    rcases exists_nat_ge X0 with ⟨Lx, hX0_le_Lx⟩
    refine ⟨max Lx 4, ?_⟩
    intro s k hs hk
    let x : ℝ := (k : ℝ) / (s : ℝ)
    have hs4 : 4 ≤ s := (Nat.le_max_right Lx 4).trans hs
    have hs3 : 3 ≤ s := by omega
    have hs_one : 1 ≤ s := by omega
    have hs_pos_nat : 0 < s := by omega
    have hs_pos_real : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hmax_le_x : ((max Lx 4 : ℕ) : ℝ) ≤ x := by
      dsimp [x]
      rw [le_div_iff₀ hs_pos_real]
      exact_mod_cast hk
    have hLx_le_max : (Lx : ℝ) ≤ ((max Lx 4 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_max_left Lx 4
    have hX0_le_x : X0 ≤ x := hX0_le_Lx.trans (hLx_le_max.trans hmax_le_x)
    rcases hscale x hX0_le_x with
      ⟨m, hm_pos, hcard, hq_le, hy_le_twoq, hq_lower, hx_ge_one,
        hlogx_ge_one, hlogq_le_logx, hlogq_pos⟩
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
    let w : ℝ := 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ)
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
        MainTheoremPolaritySetup K s q hs4 hq_card
    rcases hsetup with ⟨hG, hF, hFG⟩
    have hparams := MainTheoremPolarityParameterBounds s m hs4 hm_pos
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
    have hn3 : 3 ≤ n := by
      have ht_ge_two : 2 ≤ t := by
        dsimp [t]
        omega
      have hq_ge_two : 2 ≤ q := by
        dsimp [q]
        exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hm_pos
      have hfour_le_qt : 4 ≤ q ^ t := by
        have hpow : (2 : ℕ) ^ 2 ≤ q ^ t :=
          pow_le_pow hq_ge_two (by omega : 1 ≤ q) ht_ge_two
        norm_num at hpow ⊢
        exact hpow
      omega
    have hk1 : 1 ≤ k := by
      have hL_pos : 0 < max Lx 4 := by omega
      have hprod_pos : 0 < max Lx 4 * s := Nat.mul_pos hL_pos hs_pos_nat
      exact Nat.succ_le_iff.mpr (lt_of_lt_of_le hprod_pos hk)
    have hw_def : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ) := rfl
    have hramsey :=
      (RamseyFromGraphPair
        (LoopGraphComplement (PolarityGraph K t)) (PolarityGraph K t)
        s n dF dG k lambda lambda eta w hs3 hn3 hdG_pos hk1
        hF hG hFG heta_def hw_def heta_lower heta_upper_one).1
    -- Remaining work: prove the first-projection range hypotheses
    -- `w ≤ k` and `k ≤ eta * dF * n`, then compare the first projection's
    -- output with the general off-diagonal target.
    sorry
  rcases hnormalized with ⟨L0, hL0⟩
  refine ⟨max L0 1, ?_⟩
  intro s k hs hk
  have hL0s : L0 ≤ s := (Nat.le_max_left L0 1).trans hs
  have hL0sk : L0 * s ≤ k := by
    exact (Nat.mul_le_mul_right s (Nat.le_max_left L0 1)).trans hk
  have hs_one : 1 ≤ s := (Nat.le_max_right L0 1).trans hs
  have hs_pos_nat : 0 < s := by omega
  have hs_pos_real : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hbase_ge_one : (1 : ℝ) ≤ (k : ℝ) / (s : ℝ) := by
    have hs_le_k : s ≤ k := by
      have hs_le_max_mul : s ≤ max L0 1 * s := by
        simpa [one_mul] using Nat.mul_le_mul_right s (Nat.le_max_right L0 1)
      exact hs_le_max_mul.trans hk
    rw [le_div_iff₀ hs_pos_real]
    simpa using (by exact_mod_cast hs_le_k : (s : ℝ) ≤ (k : ℝ))
  have hexponent_le :
      (1 - delta) * (s : ℝ) ≤ (1 - delta0) * (s : ℝ) := by
    have hs_nonneg : 0 ≤ (s : ℝ) := by positivity
    nlinarith
  exact (Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexponent_le).trans
    (hL0 s k hL0s hL0sk)
