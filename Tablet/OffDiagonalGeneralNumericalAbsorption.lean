import Tablet.F2NearDiagonalLargeSPowerBound

set_option maxHeartbeats 1200000

-- [TABLET NODE: OffDiagonalGeneralNumericalAbsorption]

noncomputable section

theorem OffDiagonalGeneralNumericalAbsorption (delta : ℝ) (hdelta_pos : 0 < delta)
    (hdelta_lt : delta < 1 / 10) :
    ∃ L : ℕ, ∀ s k q : ℕ, ∀ eta w Q : ℝ, L ≤ s → L * s ≤ k →
      Q = (q : ℝ) ^ (s - 3) →
      Real.rpow ((k : ℝ) / (s : ℝ)) (1 - delta / 2) ≤ (q : ℝ) →
      0 < eta → eta ≤ 1 → eta ≤ 16 / Q →
      w ≤ delta * (k : ℝ) / 5 →
        (k : ℝ) ≤ (1 / 128) * (q : ℝ) ^ (s - 1) ∧
          Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta) * (s : ℝ)) ≤
            (1 / 50 : ℝ) * (k : ℝ) *
                Real.rpow eta ((w - (k : ℝ)) / (k : ℝ)) - 1 := by
-- BODY
  rcases F2NearDiagonalLargeSPowerBound (delta / 100) (by positivity) with
    ⟨Sgrow, hSgrow⟩
  rcases exists_nat_ge (200 / delta) with ⟨Srange, hSrange⟩
  rcases exists_nat_ge (1000 / delta) with ⟨Sfinal, hSfinal⟩
  let L : ℕ := max (max (max Sgrow Srange) Sfinal) 1600
  refine ⟨L, ?_⟩
  intro s k q eta w Q hs hk hQ_eq hq_lower heta_pos heta_le_one heta_upper hw
  let x : ℝ := (k : ℝ) / (s : ℝ)
  let a : ℝ := 1 - delta / 2
  let c : ℝ := 1 - delta / 5
  let E : ℝ := a * ((s : ℝ) - 3)
  let e : ℝ := (w - (k : ℝ)) / (k : ℝ)
  have hSgrow_le_s : Sgrow ≤ s := by
    exact (Nat.le_max_left Sgrow Srange).trans
      ((Nat.le_max_left (max Sgrow Srange) Sfinal).trans
        ((Nat.le_max_left (max (max Sgrow Srange) Sfinal) 1600).trans hs))
  have hSrange_le_s : Srange ≤ s := by
    exact (Nat.le_max_right Sgrow Srange).trans
      ((Nat.le_max_left (max Sgrow Srange) Sfinal).trans
        ((Nat.le_max_left (max (max Sgrow Srange) Sfinal) 1600).trans hs))
  have hSfinal_le_s : Sfinal ≤ s := by
    exact (Nat.le_max_right (max Sgrow Srange) Sfinal).trans
      ((Nat.le_max_left (max (max Sgrow Srange) Sfinal) 1600).trans hs)
  have h1600_le_s : 1600 ≤ s :=
    (Nat.le_max_right (max (max Sgrow Srange) Sfinal) 1600).trans hs
  have hL_pos : 0 < L := by dsimp [L]; omega
  have hs_pos_nat : 0 < s := by omega
  have hk_pos_nat : 0 < k := by
    exact lt_of_lt_of_le (Nat.mul_pos hL_pos hs_pos_nat) hk
  have hs_pos : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hk_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hx_ge_L : (L : ℝ) ≤ x := by
    dsimp [x]
    rw [le_div_iff₀ hs_pos]
    exact_mod_cast hk
  have h1600_le_L : (1600 : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast Nat.le_max_right (max (max Sgrow Srange) Sfinal) 1600
  have hx_ge_1600 : (1600 : ℝ) ≤ x := h1600_le_L.trans hx_ge_L
  have hx_ge_128 : (128 : ℝ) ≤ x := by linarith
  have hx_ge_16 : (16 : ℝ) ≤ x := by linarith
  have hx_ge_two : (2 : ℝ) ≤ x := by linarith
  have hx_ge_one : (1 : ℝ) ≤ x := by linarith
  have hx_pos : 0 < x := by linarith
  have hdelta_le : delta ≤ 1 / 10 := le_of_lt hdelta_lt
  have ha_pos : 0 < a := by dsimp [a]; nlinarith
  have ha_nonneg : 0 ≤ a := le_of_lt ha_pos
  have ha_le_one : a ≤ 1 := by dsimp [a]; nlinarith
  have hc_pos : 0 < c := by dsimp [c]; nlinarith
  have hc_nonneg : 0 ≤ c := le_of_lt hc_pos
  have hc_le_one : c ≤ 1 := by dsimp [c]; nlinarith
  have hq_pos : 0 < (q : ℝ) := by
    exact lt_of_lt_of_le (Real.rpow_pos_of_pos hx_pos a) hq_lower
  have hQ_pos : 0 < Q := by
    rw [hQ_eq]
    positivity
  have hQ_nonneg : 0 ≤ Q := le_of_lt hQ_pos
  have hRangeAbsorb :
      (k : ℝ) ≤ (1 / 128) * (q : ℝ) ^ (s - 1) := by
    let b : ℝ := delta * (s : ℝ) / 200
    have hb_nonneg : 0 ≤ b := by
      dsimp [b]
      positivity
    have hb_ge_one : 1 ≤ b := by
      have hsr_real : (200 / delta : ℝ) ≤ (s : ℝ) := by
        exact hSrange.trans (by exact_mod_cast hSrange_le_s)
      have hmul : 200 ≤ delta * (s : ℝ) := by
        rw [div_le_iff₀ hdelta_pos] at hsr_real
        simpa [mul_comm] using hsr_real
      dsimp [b]
      nlinarith
    have hs_absorb : (s : ℝ) ≤ Real.rpow x b := by
      have hs_pow2 := hSgrow s hSgrow_le_s
      have hpow2_eq :
          Real.rpow 2 ((delta / 100) * (s : ℝ) / 2) =
            Real.rpow 2 b := by
        dsimp [b]
        congr 1
        ring
      have htwo_to_x :
          Real.rpow 2 b ≤ Real.rpow x b :=
        Real.rpow_le_rpow (by norm_num) hx_ge_two hb_nonneg
      exact (hs_pow2.trans_eq hpow2_eq).trans htwo_to_x
    have hconst_absorb : (128 : ℝ) ≤ Real.rpow x b := by
      calc
        (128 : ℝ) ≤ x := hx_ge_128
        _ = Real.rpow x 1 := (Real.rpow_one x).symm
        _ ≤ Real.rpow x b :=
          Real.rpow_le_rpow_of_exponent_le hx_ge_one hb_ge_one
    have hconst_s_absorb :
        (128 : ℝ) * (s : ℝ) ≤ Real.rpow x b * Real.rpow x b := by
      exact mul_le_mul hconst_absorb hs_absorb (by positivity) (by positivity)
    have hpow_bb :
        Real.rpow x b * Real.rpow x b =
          Real.rpow x (delta * (s : ℝ) / 100) := by
      calc
        Real.rpow x b * Real.rpow x b = Real.rpow x (b + b) := by
          exact (Real.rpow_add hx_pos b b).symm
        _ = Real.rpow x (delta * (s : ℝ) / 100) := by
          congr 1
          dsimp [b]
          ring
    have hconst_s_x_absorb :
        (128 : ℝ) * (s : ℝ) * x ≤
          Real.rpow x (1 + delta * (s : ℝ) / 100) := by
      have hmulx := mul_le_mul_of_nonneg_right hconst_s_absorb (le_of_lt hx_pos)
      calc
        (128 : ℝ) * (s : ℝ) * x ≤
            (Real.rpow x b * Real.rpow x b) * x := hmulx
        _ = Real.rpow x (delta * (s : ℝ) / 100) * x := by
          rw [hpow_bb]
        _ = Real.rpow x (delta * (s : ℝ) / 100) * Real.rpow x 1 := by
          congr 1
          exact (Real.rpow_one x).symm
        _ = Real.rpow x (delta * (s : ℝ) / 100 + 1) := by
          exact (Real.rpow_add hx_pos (delta * (s : ℝ) / 100) 1).symm
        _ = Real.rpow x (1 + delta * (s : ℝ) / 100) := by ring_nf
    have hexp_le :
        1 + delta * (s : ℝ) / 100 ≤ a * ((s : ℝ) - 1) := by
      have hcoef_nonneg : 0 ≤ ((s : ℝ) - 1) / 2 + (s : ℝ) / 100 := by
        nlinarith [show (1 : ℝ) ≤ (s : ℝ) by exact_mod_cast (by omega : 1 ≤ s)]
      have hdelta_term :
          delta * (((s : ℝ) - 1) / 2 + (s : ℝ) / 100) ≤
            (1 / 10) * (((s : ℝ) - 1) / 2 + (s : ℝ) / 100) :=
        mul_le_mul_of_nonneg_right hdelta_le hcoef_nonneg
      have hs4 : (4 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 4 ≤ s)
      dsimp [a]
      nlinarith
    have hx_to_a :
        Real.rpow x (1 + delta * (s : ℝ) / 100) ≤
          Real.rpow x (a * ((s : ℝ) - 1)) :=
      Real.rpow_le_rpow_of_exponent_le hx_ge_one hexp_le
    have hcast_sub_one : ((s - 1 : ℕ) : ℝ) = (s : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega : 1 ≤ s)]
      norm_num
    have hxpow_eq :
        Real.rpow x (a * ((s : ℝ) - 1)) =
          (Real.rpow x a) ^ (s - 1) := by
      calc
        Real.rpow x (a * ((s : ℝ) - 1))
            = Real.rpow x (a * ((s - 1 : ℕ) : ℝ)) := by
              rw [hcast_sub_one]
        _ = Real.rpow (Real.rpow x a) ((s - 1 : ℕ) : ℝ) :=
              Real.rpow_mul (le_of_lt hx_pos) a ((s - 1 : ℕ) : ℝ)
        _ = (Real.rpow x a) ^ (s - 1) :=
              Real.rpow_natCast (Real.rpow x a) (s - 1)
    have hqpow :
        (Real.rpow x a) ^ (s - 1) ≤ (q : ℝ) ^ (s - 1) :=
      pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hq_lower (s - 1)
    have h128k_le : (128 : ℝ) * (k : ℝ) ≤ (q : ℝ) ^ (s - 1) := by
      have hs_mul_x : (s : ℝ) * x = (k : ℝ) := by
        dsimp [x]
        field_simp [ne_of_gt hs_pos]
      calc
        (128 : ℝ) * (k : ℝ) = (128 : ℝ) * (s : ℝ) * x := by
          rw [← hs_mul_x]
          ring
        _ ≤ Real.rpow x (1 + delta * (s : ℝ) / 100) := hconst_s_x_absorb
        _ ≤ Real.rpow x (a * ((s : ℝ) - 1)) := hx_to_a
        _ = (Real.rpow x a) ^ (s - 1) := hxpow_eq
        _ ≤ (q : ℝ) ^ (s - 1) := hqpow
    have hqpow_nonneg : 0 ≤ (q : ℝ) ^ (s - 1) := by positivity
    nlinarith
  have hFinalAbsorb :
      Real.rpow x ((1 - delta) * (s : ℝ)) ≤
        (1 / 50 : ℝ) * (k : ℝ) * Real.rpow eta e - 1 := by
    have heta_mulQ_le : eta * Q ≤ 16 := by
      rw [le_div_iff₀ hQ_pos] at heta_upper
      nlinarith
    have hQ_div_16_le_eta_inv : Q / 16 ≤ eta⁻¹ := by
      rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16)]
      rw [le_inv_mul_iff₀ heta_pos]
      nlinarith [heta_mulQ_le]
    have he_le_negc : e ≤ -c := by
      dsimp [e, c]
      rw [div_le_iff₀ hk_pos]
      nlinarith [hw]
    have hbase_eta :
        Real.rpow (Q / 16) c ≤ Real.rpow eta e := by
      have hto_inv :
          Real.rpow (Q / 16) c ≤ Real.rpow eta (-c) := by
        calc
          Real.rpow (Q / 16) c ≤ Real.rpow eta⁻¹ c :=
            Real.rpow_le_rpow (by positivity) hQ_div_16_le_eta_inv hc_nonneg
          _ = Real.rpow eta (-c) := by
            exact (Real.rpow_neg_eq_inv_rpow eta c).symm
      have hnegc_to_e : Real.rpow eta (-c) ≤ Real.rpow eta e :=
        Real.rpow_le_rpow_of_exponent_ge heta_pos heta_le_one he_le_negc
      exact hto_inv.trans hnegc_to_e
    have hs_minus_three_cast : ((s - 3 : ℕ) : ℝ) = (s : ℝ) - 3 := by
      rw [Nat.cast_sub (by omega : 3 ≤ s)]
      norm_num
    have hxE_eq :
        Real.rpow x E = (Real.rpow x a) ^ (s - 3) := by
      dsimp [E]
      calc
        Real.rpow x (a * ((s : ℝ) - 3))
            = Real.rpow x (a * ((s - 3 : ℕ) : ℝ)) := by
              rw [hs_minus_three_cast]
        _ = Real.rpow (Real.rpow x a) ((s - 3 : ℕ) : ℝ) :=
              Real.rpow_mul (le_of_lt hx_pos) a ((s - 3 : ℕ) : ℝ)
        _ = (Real.rpow x a) ^ (s - 3) :=
              Real.rpow_natCast (Real.rpow x a) (s - 3)
    have hxE_le_Q : Real.rpow x E ≤ Q := by
      have hpow : (Real.rpow x a) ^ (s - 3) ≤ (q : ℝ) ^ (s - 3) :=
        pow_le_pow_left₀ (Real.rpow_nonneg (by positivity) _) hq_lower (s - 3)
      calc
        Real.rpow x E = (Real.rpow x a) ^ (s - 3) := hxE_eq
        _ ≤ (q : ℝ) ^ (s - 3) := hpow
        _ = Q := hQ_eq.symm
    have hE_ge_one : 1 ≤ E := by
      dsimp [E, a]
      have hs1600 : (1600 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1600_le_s
      nlinarith
    have hxE_split : Real.rpow x E = Real.rpow x (E - 1) * x := by
      calc
        Real.rpow x E = Real.rpow x ((E - 1) + 1) := by ring_nf
        _ = Real.rpow x (E - 1) * Real.rpow x 1 :=
          Real.rpow_add hx_pos (E - 1) 1
        _ = Real.rpow x (E - 1) * x := by
          congr 1
          exact Real.rpow_one x
    have hxE_minus_le_Q_div :
        Real.rpow x (E - 1) ≤ Q / 16 := by
      have h16_mul : 16 * Real.rpow x (E - 1) ≤ Real.rpow x E := by
        rw [hxE_split]
        calc
          16 * Real.rpow x (E - 1) =
              Real.rpow x (E - 1) * 16 := by ring
          _ ≤ Real.rpow x (E - 1) * x :=
              mul_le_mul_of_nonneg_left hx_ge_16
                (Real.rpow_nonneg (by positivity) (E - 1))
      have h16_mul_Q : 16 * Real.rpow x (E - 1) ≤ Q := h16_mul.trans hxE_le_Q
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 16)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using h16_mul_Q
    have hx_to_eta :
        Real.rpow x ((E - 1) * c) ≤ Real.rpow eta e := by
      have hpow_left :
          Real.rpow x ((E - 1) * c) =
            Real.rpow (Real.rpow x (E - 1)) c :=
        Real.rpow_mul (le_of_lt hx_pos) (E - 1) c
      calc
        Real.rpow x ((E - 1) * c)
            = Real.rpow (Real.rpow x (E - 1)) c := hpow_left
        _ ≤ Real.rpow (Q / 16) c :=
            Real.rpow_le_rpow (Real.rpow_nonneg (by positivity) _) hxE_minus_le_Q_div
              hc_nonneg
        _ ≤ Real.rpow eta e := hbase_eta
    have hsf_real : (1000 / delta : ℝ) ≤ (s : ℝ) := by
      exact hSfinal.trans (by exact_mod_cast hSfinal_le_s)
    have hdelta_s_large : 1000 ≤ delta * (s : ℝ) := by
      rw [div_le_iff₀ hdelta_pos] at hsf_real
      simpa [mul_comm] using hsf_real
    have hgap :
        (1 - delta) * (s : ℝ) ≤ 1 + (E - 1) * c := by
      have hcoef :
          (3 / 10) * delta ≤ a * c - (1 - delta) := by
        dsimp [a, c]
        nlinarith [sq_nonneg delta]
      have hac_le_one : a * c ≤ 1 := by
        dsimp [a, c]
        nlinarith [sq_nonneg delta]
      have hconst : -3 ≤ 1 - c - 3 * (a * c) := by
        nlinarith [hc_le_one, hac_le_one]
      have hcoef_s :
          ((3 / 10) * delta) * (s : ℝ) ≤
            (a * c - (1 - delta)) * (s : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef (by positivity)
      have hgrowth : 3 ≤ (a * c - (1 - delta)) * (s : ℝ) := by
        nlinarith
      have hmain :
          0 ≤ (a * c - (1 - delta)) * (s : ℝ) + (1 - c - 3 * (a * c)) := by
        nlinarith [hgrowth, hconst]
      have hident :
          (a * c - (1 - delta)) * (s : ℝ) + (1 - c - 3 * (a * c)) =
            1 + (E - 1) * c - (1 - delta) * (s : ℝ) := by
        dsimp [E]
        ring
      nlinarith
    have htarget_to_x :
        Real.rpow x ((1 - delta) * (s : ℝ)) ≤
          Real.rpow x (1 + (E - 1) * c) :=
      Real.rpow_le_rpow_of_exponent_le hx_ge_one hgap
    have hpow_target_split :
        Real.rpow x (1 + (E - 1) * c) =
          x * Real.rpow x ((E - 1) * c) := by
      calc
        Real.rpow x (1 + (E - 1) * c)
            = Real.rpow x 1 * Real.rpow x ((E - 1) * c) :=
              Real.rpow_add hx_pos 1 ((E - 1) * c)
        _ = x * Real.rpow x ((E - 1) * c) := by
              congr 1
              exact Real.rpow_one x
    have htarget_to_eta :
        Real.rpow x ((1 - delta) * (s : ℝ)) ≤
          x * Real.rpow eta e := by
      calc
        Real.rpow x ((1 - delta) * (s : ℝ))
            ≤ Real.rpow x (1 + (E - 1) * c) := htarget_to_x
        _ = x * Real.rpow x ((E - 1) * c) := hpow_target_split
        _ ≤ x * Real.rpow eta e :=
            mul_le_mul_of_nonneg_left hx_to_eta (le_of_lt hx_pos)
    have hs_over_50_ge_two : (2 : ℝ) ≤ (s : ℝ) / 50 := by
      have hs1600 : (1600 : ℝ) ≤ (s : ℝ) := by exact_mod_cast h1600_le_s
      nlinarith
    have htarget_nonneg :
        0 ≤ Real.rpow x ((1 - delta) * (s : ℝ)) :=
      Real.rpow_nonneg (by positivity) _
    have htwo_target_le :
        2 * Real.rpow x ((1 - delta) * (s : ℝ)) ≤
          (1 / 50 : ℝ) * (k : ℝ) * Real.rpow eta e := by
      have hstep :
          Real.rpow x ((1 - delta) * (s : ℝ)) ≤ x * Real.rpow eta e :=
        htarget_to_eta
      calc
        2 * Real.rpow x ((1 - delta) * (s : ℝ))
            ≤ ((s : ℝ) / 50) * Real.rpow x ((1 - delta) * (s : ℝ)) := by
              exact mul_le_mul_of_nonneg_right hs_over_50_ge_two htarget_nonneg
        _ ≤ ((s : ℝ) / 50) * (x * Real.rpow eta e) := by
              exact mul_le_mul_of_nonneg_left hstep (by positivity)
        _ = (1 / 50 : ℝ) * (k : ℝ) * Real.rpow eta e := by
              dsimp [x]
              field_simp [ne_of_gt hs_pos]
    have htarget_ge_one :
        1 ≤ Real.rpow x ((1 - delta) * (s : ℝ)) := by
      have hexp_nonneg : 0 ≤ (1 - delta) * (s : ℝ) := by
        nlinarith
      calc
        (1 : ℝ) = Real.rpow x 0 := (Real.rpow_zero x).symm
        _ ≤ Real.rpow x ((1 - delta) * (s : ℝ)) :=
            Real.rpow_le_rpow_of_exponent_le hx_ge_one hexp_nonneg
    let T : ℝ := Real.rpow x ((1 - delta) * (s : ℝ))
    let A : ℝ := (1 / 50 : ℝ) * (k : ℝ) * Real.rpow eta e
    change T ≤ A - 1
    change 2 * T ≤ A at htwo_target_le
    change 1 ≤ T at htarget_ge_one
    linarith
  exact ⟨hRangeAbsorb, hFinalAbsorb⟩
