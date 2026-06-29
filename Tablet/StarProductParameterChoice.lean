import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductParameterChoice]

theorem StarProductParameterChoice (t : ℕ) (ht : 2 ≤ t) :
    ∃ A : ℕ, ∃ C : ℝ,
      0 < C ∧
        10128 * t ≤ A ∧
        (A : ℝ) ≤ C ∧
        4 * (A : ℝ) ≤ C ∧
        2 * (t : ℝ) * (A : ℝ) ≤ C * Real.log 2 ∧
        ∀ q : ℕ, C ≤ (q : ℝ) →
          4 ≤ q ∧
          1 ≤ Real.log (q : ℝ) ∧
          (A : ℝ) ≤ 4 * (q : ℝ) ^ (t - 1) ∧
          1 ≤ (A : ℝ) * (q : ℝ) ^ t ∧
          32 * (t : ℝ) * (q : ℝ) * Real.log (4 * (q : ℝ) ^ t) <
            ((Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ)) /
                (t + 1) - 1 : ℕ) : ℝ) := by
-- BODY
  let A : ℕ :=
    10128 * t + 100000 * t * (t + 1) * (t + 4) + (2 * (t + 1) + 2)
  let C : ℝ :=
    max 4 (max (4 * (A : ℝ))
      ((2 * (t : ℝ) * (A : ℝ)) / Real.log 2))
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hC_ge_four : (4 : ℝ) ≤ C := by
    dsimp [C]
    exact le_max_left _ _
  have hC_ge_fourA : 4 * (A : ℝ) ≤ C := by
    dsimp [C]
    exact (le_max_left _ _).trans (le_max_right _ _)
  have hC_ge_scale :
      (2 * (t : ℝ) * (A : ℝ)) / Real.log 2 ≤ C := by
    dsimp [C]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hC_pos : 0 < C := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hC_ge_four
  have hA_marked : 10128 * t ≤ A := by
    dsimp [A]
    omega
  have hA_pos_nat : 0 < A := by omega
  have hA_le_fourA : (A : ℝ) ≤ 4 * (A : ℝ) := by
    have hA_nonneg : 0 ≤ (A : ℝ) := by positivity
    nlinarith
  have hA_le_C : (A : ℝ) ≤ C := hA_le_fourA.trans hC_ge_fourA
  have hscale : 2 * (t : ℝ) * (A : ℝ) ≤ C * Real.log 2 := by
    have hmul :=
      mul_le_mul_of_nonneg_right hC_ge_scale (le_of_lt hlog2_pos)
    have hcancel :
        ((2 * (t : ℝ) * (A : ℝ)) / Real.log 2) * Real.log 2 =
          2 * (t : ℝ) * (A : ℝ) := by
      field_simp [ne_of_gt hlog2_pos]
    nlinarith
  refine ⟨A, C, hC_pos, hA_marked, hA_le_C, hC_ge_fourA, hscale, ?_⟩
  intro q hCq
  have hq_four_real : (4 : ℝ) ≤ (q : ℝ) := hC_ge_four.trans hCq
  have hq_four : 4 ≤ q := by exact_mod_cast hq_four_real
  have hq_pos_nat : 0 < q := by omega
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have hq_ne : (q : ℝ) ≠ 0 := ne_of_gt hq_pos
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hq_ge_three : (3 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 3 ≤ q)
  have hlog3_gt_one : (1 : ℝ) < Real.log 3 := by
    rw [Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 3)]
    exact Real.exp_one_lt_three
  have hlog_ge_one : 1 ≤ Real.log (q : ℝ) := by
    exact (le_of_lt hlog3_gt_one).trans
      (Real.log_le_log (by norm_num : (0 : ℝ) < 3) hq_ge_three)
  have hA_le_q : (A : ℝ) ≤ (q : ℝ) := hA_le_C.trans hCq
  have hA_delta : (A : ℝ) ≤ 4 * (q : ℝ) ^ (t - 1) := by
    have hpow_ge_q : (q : ℝ) ≤ (q : ℝ) ^ (t - 1) := by
      simpa [pow_one] using
        pow_le_pow_right₀ hq_ge_one (by omega : 1 ≤ t - 1)
    have hpow_nonneg : 0 ≤ (q : ℝ) ^ (t - 1) := by positivity
    nlinarith
  have hB_ge_one : 1 ≤ (A : ℝ) * (q : ℝ) ^ t := by
    have hA_ge_one : (1 : ℝ) ≤ (A : ℝ) := by
      exact_mod_cast (by omega : 1 ≤ A)
    have hqpow_ge_one : (1 : ℝ) ≤ (q : ℝ) ^ t := one_le_pow₀ hq_ge_one
    nlinarith
  have hexp :
      32 * (t : ℝ) * (q : ℝ) * Real.log (4 * (q : ℝ) ^ t) <
        ((Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ)) /
            (t + 1) - 1 : ℕ) : ℝ) := by
    let B : ℝ := 32 * (t : ℝ) * (q : ℝ) * Real.log (4 * (q : ℝ) ^ t)
    change B <
        ((Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ)) /
            (t + 1) - 1 : ℕ) : ℝ)
    have hqpow_ne : ((q : ℝ) ^ t) ≠ 0 := pow_ne_zero _ hq_ne
    have hlog_eq :
        Real.log (4 * (q : ℝ) ^ t) =
          Real.log 4 + (t : ℝ) * Real.log (q : ℝ) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hqpow_ne]
      rw [Real.log_pow]
    have hlog4_le : Real.log 4 ≤ 4 * Real.log (q : ℝ) := by
      have hlog4_self : Real.log 4 ≤ (4 : ℝ) :=
        Real.log_le_self (by norm_num : (0 : ℝ) ≤ 4)
      have hfour_le : (4 : ℝ) ≤ 4 * Real.log (q : ℝ) := by nlinarith
      exact hlog4_self.trans hfour_le
    have hlog_bound :
        Real.log (4 * (q : ℝ) ^ t) ≤ ((t : ℝ) + 4) * Real.log (q : ℝ) := by
      calc
        Real.log (4 * (q : ℝ) ^ t)
            = Real.log 4 + (t : ℝ) * Real.log (q : ℝ) := hlog_eq
        _ ≤ 4 * Real.log (q : ℝ) + (t : ℝ) * Real.log (q : ℝ) :=
          by nlinarith [hlog4_le]
        _ = ((t : ℝ) + 4) * Real.log (q : ℝ) := by ring
    have hB_nonneg : 0 ≤ B := by
      have hqpow_ge_one : (1 : ℝ) ≤ (q : ℝ) ^ t := one_le_pow₀ hq_ge_one
      have harg_ge_one : (1 : ℝ) ≤ 4 * (q : ℝ) ^ t := by nlinarith
      have hlog_arg_nonneg : 0 ≤ Real.log (4 * (q : ℝ) ^ t) :=
        Real.log_nonneg harg_ge_one
      dsimp [B]
      positivity
    have hB_le_norm :
        B ≤ (32 * (t : ℝ) * ((t : ℝ) + 4)) *
            ((q : ℝ) * Real.log (q : ℝ)) := by
      dsimp [B]
      calc
        32 * (t : ℝ) * (q : ℝ) * Real.log (4 * (q : ℝ) ^ t)
            ≤ 32 * (t : ℝ) * (q : ℝ) *
                (((t : ℝ) + 4) * Real.log (q : ℝ)) := by
          gcongr
        _ = (32 * (t : ℝ) * ((t : ℝ) + 4)) *
            ((q : ℝ) * Real.log (q : ℝ)) := by ring
    have hcoeff_lt :
        32 * (t : ℝ) * ((t : ℝ) + 1) * ((t : ℝ) + 4) +
            (2 * ((t : ℝ) + 1) + 1) < (A : ℝ) := by
      dsimp [A]
      norm_num
      have hprod : 0 ≤ (t : ℝ) * ((t : ℝ) + 1) * ((t : ℝ) + 4) := by positivity
      nlinarith
    have hqlog_ge_one : 1 ≤ (q : ℝ) * Real.log (q : ℝ) := by nlinarith
    have hqlog_pos : 0 < (q : ℝ) * Real.log (q : ℝ) := by nlinarith
    have hlarge :
        ((t + 1 : ℕ) : ℝ) * (B + 2) + 1 <
          (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) := by
      have hmain_bound :
          ((t + 1 : ℕ) : ℝ) * (B + 2) + 1 ≤
            (32 * (t : ℝ) * ((t : ℝ) + 1) * ((t : ℝ) + 4) +
                (2 * ((t : ℝ) + 1) + 1)) *
              ((q : ℝ) * Real.log (q : ℝ)) := by
        have ht1_nonneg : 0 ≤ (t : ℝ) + 1 := by positivity
        have hB_scaled :
            ((t : ℝ) + 1) * B ≤
              ((t : ℝ) + 1) *
                ((32 * (t : ℝ) * ((t : ℝ) + 4)) *
                  ((q : ℝ) * Real.log (q : ℝ))) :=
          mul_le_mul_of_nonneg_left hB_le_norm ht1_nonneg
        have ht1_cast : ((t + 1 : ℕ) : ℝ) = (t : ℝ) + 1 := by norm_num
        nlinarith
      have hmul_lt :
          (32 * (t : ℝ) * ((t : ℝ) + 1) * ((t : ℝ) + 4) +
                (2 * ((t : ℝ) + 1) + 1)) *
              ((q : ℝ) * Real.log (q : ℝ)) <
            (A : ℝ) * ((q : ℝ) * Real.log (q : ℝ)) :=
        mul_lt_mul_of_pos_right hcoeff_lt hqlog_pos
      nlinarith
    let d : ℕ := t + 1
    have hd : 0 < d := by dsimp [d]; omega
    let x : ℝ := (A : ℝ) * (q : ℝ) * Real.log (q : ℝ)
    have hlarge' : (d : ℝ) * (B + 2) + 1 < x := by
      simpa [d, x] using hlarge
    let n : ℕ := Nat.floor x
    have hfloor_gt : (d : ℝ) * (B + 2) < (n : ℝ) := by
      have hlt : (d : ℝ) * (B + 2) < x - 1 := by linarith
      exact hlt.trans (Nat.sub_one_lt_floor x)
    have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
    have hb2_lt : B + 2 < (n : ℝ) / (d : ℝ) := by
      exact (lt_div_iff₀ hdR).mpr (by simpa [mul_comm] using hfloor_gt)
    have hquot_upper :
        (n : ℝ) / (d : ℝ) < ((n / d : ℕ) : ℝ) + 1 := by
      have hnat : n < (n / d + 1) * d := by
        have hmod : n % d < d := Nat.mod_lt n hd
        calc
          n = d * (n / d) + n % d := by
            rw [Nat.div_add_mod]
          _ < d * (n / d) + d := Nat.add_lt_add_left hmod _
          _ = (n / d + 1) * d := by ring
      have hreal : (n : ℝ) < ((n / d + 1) * d : ℕ) := by
        exact_mod_cast hnat
      have hmul : (n : ℝ) < (((n / d : ℕ) : ℝ) + 1) * (d : ℝ) := by
        simpa [Nat.cast_add, Nat.cast_mul, add_mul, mul_comm, mul_left_comm,
          mul_assoc] using hreal
      exact (div_lt_iff₀ hdR).mpr hmul
    have hquot_gt : B + 1 < ((n / d : ℕ) : ℝ) := by linarith
    have hquot_ge_one_nat : 1 ≤ n / d := by
      have h1 : (1 : ℝ) < ((n / d : ℕ) : ℝ) := by linarith
      exact_mod_cast (le_of_lt h1)
    rw [show Nat.floor x = n by rfl]
    rw [Nat.cast_sub hquot_ge_one_nat]
    dsimp [d, x]
    linarith
  exact ⟨hq_four, hlog_ge_one, hA_delta, hB_ge_one, hexp⟩
