import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductFloorWeightSideConditions]

theorem StarProductFloorWeightSideConditions (A t q : ℕ)
    (ht : 1 ≤ t) (hq : 1 ≤ q)
    (hexp :
      32 * (t : ℝ) * (q : ℝ) * Real.log (4 * (q : ℝ) ^ t) <
        (((Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ)) /
            (t + 1) - 1 : ℕ) : ℝ))) :
    let w : ℕ := Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ))
    (w : ℝ) ≤ (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) ∧
      (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) ^ (w / (t + 1) - 1) <
        1 / (4 * (q : ℝ) ^ t) := by
-- BODY
  let w : ℕ := Nat.floor ((A : ℝ) * (q : ℝ) * Real.log (q : ℝ))
  change
    (w : ℝ) ≤ (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) ∧
      (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) ^ (w / (t + 1) - 1) <
        1 / (4 * (q : ℝ) ^ t)
  have hq_ge_one : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hlogq_nonneg : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq_ge_one
  have hfloor_arg_nonneg :
      0 ≤ (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) := by positivity
  have hw :
      (w : ℝ) ≤ (A : ℝ) * (q : ℝ) * Real.log (q : ℝ) := by
    exact Nat.floor_le hfloor_arg_nonneg
  let e : ℕ := w / (t + 1) - 1
  have hexp_e :
      32 * (t : ℝ) * (q : ℝ) * Real.log (4 * (q : ℝ) ^ t) < (e : ℝ) := by
    simpa [e, w] using hexp
  have ht_pos : 0 < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one ht)
  have hq_pos : 0 < (q : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  let D : ℝ := 32 * (t : ℝ) * (q : ℝ)
  let M : ℝ := 4 * (q : ℝ) ^ t
  have hD_pos : 0 < D := by positivity
  have hD_ge_one : (1 : ℝ) ≤ D := by
    have ht_ge_one : (1 : ℝ) ≤ t := by exact_mod_cast ht
    have hq_ge_one' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    dsimp [D]
    nlinarith [ht_ge_one, hq_ge_one']
  have hx_le_one : 1 / D ≤ 1 := by
    rw [div_le_one hD_pos]
    exact hD_ge_one
  have hbase_nonneg : 0 ≤ 1 - 1 / D := by linarith
  have hpow_le :
      (1 - 1 / D) ^ e ≤ Real.exp (-(1 / D)) ^ e := by
    exact pow_le_pow_left₀ hbase_nonneg
      (by linarith [Real.add_one_le_exp (-(1 / D))]) e
  have hM_pos : 0 < M := by positivity
  have hlog_lt : Real.log M < (e : ℝ) * (1 / D) := by
    have hexpD : D * Real.log M < (e : ℝ) := by
      simpa [D, M, mul_assoc] using hexp_e
    have hdiv := (div_lt_div_iff_of_pos_right hD_pos).mpr hexpD
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    have hleft : D * Real.log M / D = Real.log M := by
      field_simp [hD_ne]
    have hright : (e : ℝ) / D = (e : ℝ) * (1 / D) := by ring
    simpa [hleft, hright] using hdiv
  have hexp_lt :
      Real.exp (-(1 / D)) ^ e < 1 / M := by
    rw [← Real.exp_nat_mul]
    have harg : (e : ℝ) * (-(1 / D)) < -Real.log M := by
      nlinarith
    have htarget : 1 / M = Real.exp (-Real.log M) := by
      simp [one_div, Real.exp_neg, Real.exp_log hM_pos]
    rw [htarget]
    exact Real.exp_lt_exp.mpr harg
  have hfactor :
      (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) ^ (w / (t + 1) - 1) <
        1 / (4 * (q : ℝ) ^ t) := by
    calc
      (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) ^ (w / (t + 1) - 1)
          = (1 - 1 / D) ^ e := by simp [D, e]
      _ ≤ Real.exp (-(1 / D)) ^ e := hpow_le
      _ < 1 / M := hexp_lt
      _ = 1 / (4 * (q : ℝ) ^ t) := by simp [M]
  exact ⟨hw, hfactor⟩
