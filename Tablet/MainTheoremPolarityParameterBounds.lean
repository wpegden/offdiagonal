import Mathlib.Algebra.Ring.GeomSum
import Tablet.Preamble

-- [TABLET NODE: MainTheoremPolarityParameterBounds]

noncomputable section

open Finset

theorem MainTheoremPolarityParameterBounds (s m : ℕ) (hs : 4 ≤ s) (hm : 1 ≤ m) :
    let t := s - 2
    let q := 2 ^ m
    let n := (q ^ (t + 1) - 1) / (q - 1)
    let dG := (q ^ t - 1) / (q - 1)
    let dF := n - dG
    let a := (q ^ (t - 1) - 1) / (q - 1)
    let lambda := Real.sqrt (((dG - a : ℕ) : ℝ))
    let Q := ((q ^ (t - 1) : ℕ) : ℝ)
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
-- BODY
  dsimp
  let t := s - 2
  let q := 2 ^ m
  have ht : 2 ≤ t := by dsimp [t]; omega
  have hq2 : 2 ≤ q := by
    dsimp [q]
    exact Nat.pow_le_pow_right (by omega : 1 ≤ (2 : ℕ)) hm
  have hq1 : 1 ≤ q := by omega
  let n := (q ^ (t + 1) - 1) / (q - 1)
  let dG := (q ^ t - 1) / (q - 1)
  let dF := n - dG
  let a := (q ^ (t - 1) - 1) / (q - 1)
  let lambda := Real.sqrt (((dG - a : ℕ) : ℝ))
  let Q : ℝ := ((q ^ (t - 1) : ℕ) : ℝ)
  have hn_sum : n = ∑ i ∈ range (t + 1), q ^ i := by
    dsimp [n]
    rw [Nat.geomSum_eq hq2]
  have hdG_sum : dG = ∑ i ∈ range t, q ^ i := by
    dsimp [dG]
    rw [Nat.geomSum_eq hq2]
  have ha_sum : a = ∑ i ∈ range (t - 1), q ^ i := by
    dsimp [a]
    rw [Nat.geomSum_eq hq2]
  have hn_eq : n = dG + q ^ t := by
    rw [hn_sum, hdG_sum, sum_range_succ]
  have hdG_eq : dG = a + q ^ (t - 1) := by
    have ht_eq : t = (t - 1) + 1 := by omega
    have hdG_sum' : dG = ∑ i ∈ range ((t - 1) + 1), q ^ i := by
      rw [← ht_eq]
      exact hdG_sum
    rw [hdG_sum', ha_sum, sum_range_succ]
  have hdF_eq : dF = q ^ t := by
    dsimp [dF]
    omega
  have hdiff_eq : (dG - a : ℕ) = q ^ (t - 1) := by omega
  have hn_lower : q ^ t ≤ n := by omega
  have hn_upper : n ≤ (t + 1) * q ^ t := by
    rw [hn_sum]
    calc
      ∑ i ∈ range (t + 1), q ^ i ≤ ∑ i ∈ range (t + 1), q ^ t := by
        apply sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right hq1 (by simp at hi; omega)
      _ = (t + 1) * q ^ t := by simp
  have hdG_lower : q ^ (t - 1) ≤ dG := by omega
  have hdG_upper : dG ≤ t * q ^ (t - 1) := by
    rw [hdG_sum]
    calc
      ∑ i ∈ range t, q ^ i ≤ ∑ i ∈ range t, q ^ (t - 1) := by
        apply sum_le_sum
        intro i hi
        exact Nat.pow_le_pow_right hq1 (by simp at hi; omega)
      _ = t * q ^ (t - 1) := by simp
  have hn_pos : 0 < n := by
    exact lt_of_lt_of_le (pow_pos (by omega : 0 < q) t) hn_lower
  have hdF_pos : 0 < dF := by
    rw [hdF_eq]
    exact pow_pos (by omega : 0 < q) t
  have hdG_pos : 0 < dG := by
    exact lt_of_lt_of_le (pow_pos (by omega : 0 < q) (t - 1)) hdG_lower
  have hlambda_sq :
      lambda ^ 2 = Q := by
    dsimp [lambda, Q]
    rw [hdiff_eq]
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  have hQ_pos : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (pow_pos (by omega : 0 < q) (t - 1))
  have hQ_nonneg : 0 ≤ Q := le_of_lt hQ_pos
  have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
  have hdFR_pos : (0 : ℝ) < dF := by exact_mod_cast hdF_pos
  have hdGR_pos : (0 : ℝ) < dG := by exact_mod_cast hdG_pos
  have hdGR_nonneg : (0 : ℝ) ≤ dG := le_of_lt hdGR_pos
  have hQ_le_dG : Q ≤ (dG : ℝ) := by
    dsimp [Q]
    exact_mod_cast hdG_lower
  have hdG_le_n : (dG : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (by omega : dG ≤ n)
  have hQ_ge_one : (1 : ℝ) ≤ Q := by
    dsimp [Q]
    exact_mod_cast (Nat.succ_le_iff.mpr (pow_pos (by omega : 0 < q) (t - 1)))
  have hdF_ge_Q : Q ≤ (dF : ℝ) := by
    dsimp [Q]
    rw [hdF_eq]
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 1 ≤ q) (by omega : t - 1 ≤ t))
  have hfirst_lower :
      1 / (n : ℝ) ^ 2 ≤ lambda ^ 2 / (dG : ℝ) ^ 2 := by
    rw [hlambda_sq]
    have hsquares : (dG : ℝ) ^ 2 ≤ (n : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hdG_le_n)
        (add_nonneg hdGR_nonneg (le_of_lt hnR_pos))]
    have hrecip : 1 / (n : ℝ) ^ 2 ≤ 1 / (dG : ℝ) ^ 2 :=
      one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (dG : ℝ) ^ 2) hsquares
    have hone_le :
        1 / (dG : ℝ) ^ 2 ≤ Q / (dG : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hQ_ge_one (by positivity)
    exact hrecip.trans hone_le
  have hfirst_upper :
      lambda ^ 2 / (dG : ℝ) ^ 2 ≤ 1 := by
    rw [hlambda_sq]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (dG : ℝ) ^ 2)]
    have hdG_le_square : (dG : ℝ) ≤ (dG : ℝ) ^ 2 := by
      nlinarith [mul_nonneg
        (sub_nonneg.mpr
          (by exact_mod_cast (Nat.succ_le_iff.mp hdG_pos) : (1 : ℝ) ≤ dG))
        hdGR_nonneg]
    nlinarith
  have hsecond_upper :
      lambda * lambda / ((dF : ℝ) * (dG : ℝ)) ≤ 1 := by
    calc
      lambda * lambda / ((dF : ℝ) * (dG : ℝ))
          = lambda ^ 2 / ((dF : ℝ) * (dG : ℝ)) := by ring
      _ = Q / ((dF : ℝ) * (dG : ℝ)) := by rw [hlambda_sq]
      _ ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (dF : ℝ) * (dG : ℝ))]
        have hdG_le_mul : (dG : ℝ) ≤ (dF : ℝ) * (dG : ℝ) := by
          nlinarith [mul_nonneg
            (sub_nonneg.mpr
              (by exact_mod_cast (Nat.succ_le_iff.mp hdF_pos) : (1 : ℝ) ≤ dF))
            hdGR_nonneg]
        nlinarith
  have hfirst_eta :
      lambda ^ 2 / (dG : ℝ) ^ 2 ≤ 1 / Q := by
    rw [hlambda_sq]
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (dG : ℝ) ^ 2) hQ_pos]
    have hsquare : Q * Q ≤ (dG : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hQ_le_dG)
        (add_nonneg hQ_nonneg hdGR_nonneg)]
    simpa [pow_two] using hsquare
  have hsecond_eta :
      lambda * lambda / ((dF : ℝ) * (dG : ℝ)) ≤ 1 / Q := by
    calc
      lambda * lambda / ((dF : ℝ) * (dG : ℝ))
          = lambda ^ 2 / ((dF : ℝ) * (dG : ℝ)) := by ring
      _ = Q / ((dF : ℝ) * (dG : ℝ)) := by rw [hlambda_sq]
      _ ≤ 1 / Q := by
        rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < (dF : ℝ) * (dG : ℝ)) hQ_pos]
        have hprod : Q * Q ≤ (dF : ℝ) * (dG : ℝ) := by
          nlinarith [mul_nonneg (sub_nonneg.mpr hdF_ge_Q) hdGR_nonneg,
            mul_nonneg hQ_nonneg (sub_nonneg.mpr hQ_le_dG)]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
  have heta_upper :
      max (lambda ^ 2 / (dG : ℝ) ^ 2)
        (lambda * lambda / ((dF : ℝ) * (dG : ℝ))) ≤ 1 / Q :=
    max_le hfirst_eta hsecond_eta
  exact ⟨hn_pos, hdF_pos, hdG_pos, hn_lower, hn_upper, hdG_lower, hdG_upper,
    hdF_eq, hdiff_eq, hlambda_sq, hQ_pos, hfirst_lower, hfirst_upper, hsecond_upper,
    heta_upper⟩
