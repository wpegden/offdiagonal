import Tablet.Preamble

-- [TABLET NODE: CloseToDiagonalTargetScaleLarge]

open Filter in
theorem CloseToDiagonalTargetScaleLarge (eps delta : ℝ) (heps : 0 < eps)
    (hdelta_nonneg : 0 ≤ delta) (hdelta_le : delta ≤ 1 / 2) :
    ∃ s0 : ℕ, 4 ≤ s0 ∧ ∀ s a : ℕ, s0 ≤ s →
      (a : ℝ) ≤ delta * (s : ℝ) →
      2 / eps ≤
        ((s : ℝ) / Real.exp 1) *
          Real.rpow 2
            ((((s : ℝ) + (a : ℝ) - 1) / 2) -
              ((a : ℝ) ^ 2) / (2 * (s : ℝ))) := by
-- BODY
  have heps_ne : eps ≠ 0 := ne_of_gt heps
  let c : ℝ := Real.log 2 / 4
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hlin : Tendsto (fun s : ℕ => c * (s : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hexp_tendsto : Tendsto (fun s : ℕ => Real.exp (c * (s : ℝ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp hlin
  rcases eventually_atTop.1 ((tendsto_atTop.1 hexp_tendsto) ((2 / eps) * Real.exp 1)) with
    ⟨N, hN⟩
  refine ⟨max N 4, Nat.le_max_right N 4, ?_⟩
  intro s a hs ha
  have hsN : N ≤ s := le_trans (Nat.le_max_left N 4) hs
  have hs4 : 4 ≤ s := le_trans (Nat.le_max_right N 4) hs
  have hspos_nat : 0 < s := by omega
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
  have hsone : (1 : ℝ) ≤ (s : ℝ) := by exact_mod_cast (by omega : 1 ≤ s)
  have ha_nonneg : 0 ≤ (a : ℝ) := by positivity
  have hgrowth : (2 / eps) * Real.exp 1 ≤ Real.exp (c * (s : ℝ)) := hN s hsN
  have hgrowth_div : 2 / eps ≤ Real.exp (c * (s : ℝ)) / Real.exp 1 := by
    rw [le_div_iff₀ (Real.exp_pos 1)]
    simpa [mul_comm, mul_left_comm, mul_assoc] using hgrowth
  have hpow_quarter :
      Real.rpow 2 ((s : ℝ) / 4) = Real.exp (c * (s : ℝ)) := by
    change (2 : ℝ) ^ ((s : ℝ) / 4) = Real.exp (c * (s : ℝ))
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [c]
    ring_nf
  have hexponent_lower :
      (s : ℝ) / 4 ≤
        (((s : ℝ) + (a : ℝ) - 1) / 2) -
          ((a : ℝ) ^ 2) / (2 * (s : ℝ)) := by
    field_simp [hspos.ne']
    ring_nf
    nlinarith [ha, hdelta_nonneg, hdelta_le, ha_nonneg, hspos.le,
      show (4 : ℝ) ≤ (s : ℝ) by exact_mod_cast hs4]
  have hrpow_lower :
      Real.rpow 2 ((s : ℝ) / 4) ≤
        Real.rpow 2
          ((((s : ℝ) + (a : ℝ) - 1) / 2) -
            ((a : ℝ) ^ 2) / (2 * (s : ℝ))) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexponent_lower
  have hcoef : (1 / Real.exp 1) ≤ (s : ℝ) / Real.exp 1 := by
    exact div_le_div_of_nonneg_right hsone (Real.exp_pos 1).le
  calc
    2 / eps ≤ Real.exp (c * (s : ℝ)) / Real.exp 1 := hgrowth_div
    _ = (1 / Real.exp 1) * Real.rpow 2 ((s : ℝ) / 4) := by
      rw [hpow_quarter]
      ring
    _ ≤ ((s : ℝ) / Real.exp 1) * Real.rpow 2 ((s : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hcoef (Real.rpow_nonneg (by norm_num) _)
    _ ≤ ((s : ℝ) / Real.exp 1) *
        Real.rpow 2
          ((((s : ℝ) + (a : ℝ) - 1) / 2) -
            ((a : ℝ) ^ 2) / (2 * (s : ℝ))) :=
      mul_le_mul_of_nonneg_left hrpow_lower (by positivity)
