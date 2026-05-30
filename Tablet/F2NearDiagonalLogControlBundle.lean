import Tablet.F2NearDiagonalSmallXLogBound
import Tablet.F2NearDiagonalLogSquareBound
import Tablet.F2NearDiagonalBinomialLogBound
import Tablet.F2NearDiagonalChooseSymmetry
import Tablet.F2NearDiagonalQuadraticMaxBound

-- [TABLET NODE: F2NearDiagonalLogControlBundle]

theorem F2NearDiagonalLogControlBundle (eps : ℝ) (heps : 0 < eps) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ s0 : ℕ,
      ∀ s a t : ℕ, s0 ≤ s → (a : ℝ) ≤ delta * (s : ℝ) →
        t ∈ Finset.Icc 1 (s - 1) →
          ∃ lambda : ℝ,
            ((Nat.choose (s + a) t : ℕ) : ℝ) ≤
              Real.rpow 2 (((a : ℝ) + ((s - t : ℕ) : ℝ)) * lambda) ∧
            (a : ℝ) * lambda ≤ eps * (s : ℝ) / 4 ∧
            ((s - t : ℕ) : ℝ) * lambda +
              (3 / 2 : ℝ) * ((s - t : ℕ) : ℝ) -
                ((s - t : ℕ) : ℝ) ^ 2 / 2 ≤ eps * (s : ℝ) / 4 := by
-- BODY
  rcases F2NearDiagonalSmallXLogBound eps heps with ⟨delta, hdelta_pos, hdelta_le_one, hsmall⟩
  rcases F2NearDiagonalLogSquareBound eps heps with ⟨sLog, hlogSq⟩
  refine ⟨delta, hdelta_pos, max sLog 1, ?_⟩
  intro s a t hs ha ht
  let j : ℕ := s - t
  let lambda : ℝ :=
    Real.logb 2 (Real.exp 1 * ((s + a : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ))
  have hs_one : 1 ≤ s := le_trans (Nat.le_max_right sLog 1) hs
  have hspos_nat : 0 < s := by omega
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
  have hs_nonneg : 0 ≤ (s : ℝ) := hspos.le
  have hdelta_s_le_s : delta * (s : ℝ) ≤ (s : ℝ) := by
    have := mul_le_mul_of_nonneg_right hdelta_le_one hs_nonneg
    simpa using this
  have ha_le_s : (a : ℝ) ≤ (s : ℝ) := ha.trans hdelta_s_le_s
  have hsa_le_two_s : ((s + a : ℕ) : ℝ) ≤ 2 * (s : ℝ) := by
    norm_num [Nat.cast_add]
    linarith
  have ht_bounds := Finset.mem_Icc.mp ht
  have ht_one : 1 ≤ t := ht_bounds.1
  have ht_le : t ≤ s - 1 := ht_bounds.2
  have hj_pos : 0 < j := by
    dsimp [j]
    omega
  have hj_le_s : j ≤ s := by
    dsimp [j]
    omega
  have hsub : s - j = t := by
    dsimp [j]
    omega
  have hsym : Nat.choose (s + a) t = Nat.choose (s + a) (j + a) := by
    have h := F2NearDiagonalChooseSymmetry s a j hj_le_s
    simpa [hsub] using h
  have hR_pos :
      0 < Real.exp 1 * ((s + a : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ) := by
    positivity
  have hR_le_Larg :
      Real.exp 1 * ((s + a : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ) ≤
        2 * Real.exp 1 * (s : ℝ) := by
    have hnum_nonneg : 0 ≤ Real.exp 1 * ((s + a : ℕ) : ℝ) := by positivity
    have hden_ge_one : (1 : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by norm_num
    calc
      Real.exp 1 * ((s + a : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)
          ≤ Real.exp 1 * ((s + a : ℕ) : ℝ) / (1 : ℝ) :=
            div_le_div_of_nonneg_left hnum_nonneg zero_lt_one hden_ge_one
      _ = Real.exp 1 * ((s + a : ℕ) : ℝ) := by ring
      _ ≤ Real.exp 1 * (2 * (s : ℝ)) :=
            mul_le_mul_of_nonneg_left hsa_le_two_s (Real.exp_pos 1).le
      _ = 2 * Real.exp 1 * (s : ℝ) := by ring
  have hLarg_pos : 0 < 2 * Real.exp 1 * (s : ℝ) := by positivity
  have hlambda_le_L :
      lambda ≤ Real.logb 2 (2 * Real.exp 1 * (s : ℝ)) := by
    dsimp [lambda]
    exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hR_pos hR_le_Larg
  refine ⟨lambda, ?_, ?_, ?_⟩
  · have hbinom :=
      F2NearDiagonalBinomialLogBound (s + a) (j + a) (a + 1)
        (by omega : 0 < j + a) (by omega : 0 < a + 1) (by omega : a + 1 ≤ j + a)
    calc
      ((Nat.choose (s + a) t : ℕ) : ℝ) =
          ((Nat.choose (s + a) (j + a) : ℕ) : ℝ) := by rw [hsym]
      _ ≤ Real.rpow 2 (((j + a : ℕ) : ℝ) * lambda) := by
          simpa [lambda] using hbinom
      _ = Real.rpow 2 (((a : ℝ) + (j : ℝ)) * lambda) := by
          congr 1
          norm_num [Nat.cast_add, add_comm, add_left_comm]
  · by_cases ha_zero : a = 0
    · subst a
      have hnonneg : 0 ≤ eps * (s : ℝ) / 4 := by positivity
      simpa [lambda] using hnonneg
    · have hapos_nat : 0 < a := Nat.pos_of_ne_zero ha_zero
      have hapos : 0 < (a : ℝ) := by exact_mod_cast hapos_nat
      let x : ℝ := (a : ℝ) / (s : ℝ)
      have hxpos : 0 < x := div_pos hapos hspos
      have hxle_delta : x ≤ delta := by
        dsimp [x]
        rw [div_le_iff₀ hspos]
        simpa [mul_comm] using ha
      have hsmallx := hsmall x hxpos hxle_delta
      have ha_le_asucc : (a : ℝ) ≤ ((a + 1 : ℕ) : ℝ) := by norm_num
      have hR_le_small :
          Real.exp 1 * ((s + a : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ) ≤
            2 * Real.exp 1 / x := by
        have hnum_nonneg : 0 ≤ Real.exp 1 * ((s + a : ℕ) : ℝ) := by positivity
        calc
          Real.exp 1 * ((s + a : ℕ) : ℝ) / ((a + 1 : ℕ) : ℝ)
              ≤ Real.exp 1 * ((s + a : ℕ) : ℝ) / (a : ℝ) :=
                div_le_div_of_nonneg_left hnum_nonneg hapos ha_le_asucc
          _ ≤ Real.exp 1 * (2 * (s : ℝ)) / (a : ℝ) :=
                div_le_div_of_nonneg_right
                  (mul_le_mul_of_nonneg_left hsa_le_two_s (Real.exp_pos 1).le) hapos.le
          _ = 2 * Real.exp 1 / x := by
                dsimp [x]
                field_simp [hapos.ne', hspos.ne']
      have hxarg_pos : 0 < 2 * Real.exp 1 / x := by positivity
      have hlambda_le_small :
          lambda ≤ Real.logb 2 (2 * Real.exp 1 / x) := by
        dsimp [lambda]
        exact Real.logb_le_logb_of_le (by norm_num : (1 : ℝ) < 2) hR_pos hR_le_small
      have hx_lambda :
          x * lambda ≤ x * Real.logb 2 (2 * Real.exp 1 / x) :=
        mul_le_mul_of_nonneg_left hlambda_le_small hxpos.le
      have hx_control : x * lambda ≤ eps / 4 := hx_lambda.trans hsmallx
      have hsx_eq_a : (s : ℝ) * x = (a : ℝ) := by
        dsimp [x]
        field_simp [hspos.ne']
      calc
        (a : ℝ) * lambda = (s : ℝ) * (x * lambda) := by
          rw [← hsx_eq_a]
          ring
        _ ≤ (s : ℝ) * (eps / 4) :=
          mul_le_mul_of_nonneg_left hx_control hs_nonneg
        _ = eps * (s : ℝ) / 4 := by ring
  · have hquad :=
      F2NearDiagonalQuadraticMaxBound lambda (Real.logb 2 (2 * Real.exp 1 * (s : ℝ)))
        (j : ℝ) hlambda_le_L (by positivity)
    have hsLog : sLog ≤ s := le_trans (Nat.le_max_left sLog 1) hs
    have hlarge := hlogSq s hsLog
    exact hquad.trans hlarge
