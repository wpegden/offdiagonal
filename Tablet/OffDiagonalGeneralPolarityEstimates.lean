import Mathlib.Algebra.Ring.GeomSum
import Tablet.MainTheoremPolarityParameterBounds

-- [TABLET NODE: OffDiagonalGeneralPolarityEstimates]

noncomputable section

open Finset

theorem OffDiagonalGeneralPolarityEstimates (s m : ℕ) (hs : 4 ≤ s) (hm : 1 ≤ m) :
    let t := s - 2
    let q := 2 ^ m
    let n := (q ^ (t + 1) - 1) / (q - 1)
    let dG := (q ^ t - 1) / (q - 1)
    let dF : ℕ := n - dG
    let a : ℕ := (q ^ (t - 1) - 1) / (q - 1)
    let lambda := Real.sqrt (((dG - a : ℕ) : ℝ))
    let Q : ℝ := ((q ^ (t - 1) : ℕ) : ℝ)
    let eta : ℝ :=
      max (lambda ^ 2 / (dG : ℝ) ^ 2)
        (lambda * lambda / ((dF : ℝ) * (dG : ℝ)))
    q ^ t ≤ n ∧ n ≤ 2 * q ^ t ∧
      q ^ (t - 1) ≤ dG ∧ dG ≤ 2 * q ^ (t - 1) ∧
      dF = q ^ t ∧ lambda ^ 2 = Q ∧
      (n : ℝ) / 2 ≤ (dF : ℝ) ∧
      1 / (16 * Q) ≤ eta ∧ eta ≤ 16 / Q := by
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
  let eta : ℝ :=
    max (lambda ^ 2 / (dG : ℝ) ^ 2)
      (lambda * lambda / ((dF : ℝ) * (dG : ℝ)))
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
    ⟨hn_pos, hdF_pos, hdG_pos, hn_lower, _hn_upper_old, hdG_lower,
      _hdG_upper_old, hdF_eq, _hdiff_eq, hlambda_sq, hQ_pos, _hfirst_lower,
      _hfirst_upper, _hsecond_upper, heta_upper_Q⟩
  have hsum_le_two_last :
      ∀ r : ℕ, ∑ i ∈ range (r + 1), q ^ i ≤ 2 * q ^ r := by
    intro r
    induction r with
    | zero =>
        simp
    | succ r ih =>
        rw [sum_range_succ]
        calc
          (∑ i ∈ range (r + 1), q ^ i) + q ^ (r + 1)
              ≤ 2 * q ^ r + q ^ (r + 1) := by
                exact Nat.add_le_add_right ih _
          _ = (2 + q) * q ^ r := by
                rw [pow_succ]
                ring
          _ ≤ (2 * q) * q ^ r := by
                exact Nat.mul_le_mul_right (q ^ r) (by omega : 2 + q ≤ 2 * q)
          _ = 2 * (q * q ^ r) := by ring
          _ = 2 * q ^ (r + 1) := by
                rw [pow_succ]
                ring
  have hn_sum : n = ∑ i ∈ range (t + 1), q ^ i := by
    dsimp [n]
    rw [Nat.geomSum_eq hq2]
  have hdG_sum : dG = ∑ i ∈ range t, q ^ i := by
    dsimp [dG]
    rw [Nat.geomSum_eq hq2]
  have hn_upper_two : n ≤ 2 * q ^ t := by
    rw [hn_sum]
    exact hsum_le_two_last t
  have hdG_upper_two : dG ≤ 2 * q ^ (t - 1) := by
    have ht_eq : t = (t - 1) + 1 := by omega
    rw [hdG_sum, ht_eq]
    exact hsum_le_two_last (t - 1)
  have hdF_ge_half_n : (n : ℝ) / 2 ≤ (dF : ℝ) := by
    rw [hdF_eq]
    have hn_upper_real : (n : ℝ) ≤ (2 * q ^ t : ℕ) := by exact_mod_cast hn_upper_two
    norm_num at hn_upper_real ⊢
    linarith
  have hfirst_le_eta :
      lambda ^ 2 / (dG : ℝ) ^ 2 ≤ eta := by
    dsimp [eta]
    exact le_max_left _ _
  have hfirst_eq_Q :
      lambda ^ 2 / (dG : ℝ) ^ 2 = Q / (dG : ℝ) ^ 2 := by
    rw [hlambda_sq]
  have hdGR_pos : (0 : ℝ) < dG := by exact_mod_cast hdG_pos
  have hdGR_nonneg : (0 : ℝ) ≤ dG := le_of_lt hdGR_pos
  have hdG_le_twoQ : (dG : ℝ) ≤ 2 * Q := by
    dsimp [Q]
    exact_mod_cast hdG_upper_two
  have hdG_sq_le : (dG : ℝ) ^ 2 ≤ (2 * Q) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hdG_le_twoQ)
      (add_nonneg (by positivity : (0 : ℝ) ≤ 2 * Q) hdGR_nonneg)]
  have hquarter_le_first : 1 / (4 * Q) ≤ Q / (dG : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Q)
      (by positivity : (0 : ℝ) < (dG : ℝ) ^ 2)]
    nlinarith
  have hsixteenth_le_quarter : 1 / (16 * Q) ≤ 1 / (4 * Q) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 16 * Q)
      (by positivity : (0 : ℝ) < 4 * Q)]
    nlinarith
  have heta_lower : 1 / (16 * Q) ≤ eta := by
    calc
      1 / (16 * Q) ≤ 1 / (4 * Q) := hsixteenth_le_quarter
      _ ≤ Q / (dG : ℝ) ^ 2 := hquarter_le_first
      _ = lambda ^ 2 / (dG : ℝ) ^ 2 := hfirst_eq_Q.symm
      _ ≤ eta := hfirst_le_eta
  have heta_upper : eta ≤ 16 / Q := by
    have hle : 1 / Q ≤ 16 / Q := by
      rw [div_le_div_iff₀ hQ_pos hQ_pos]
      nlinarith
    exact heta_upper_Q.trans hle
  exact ⟨hn_lower, hn_upper_two, hdG_lower, hdG_upper_two, hdF_eq, hlambda_sq,
    hdF_ge_half_n, heta_lower, heta_upper⟩
