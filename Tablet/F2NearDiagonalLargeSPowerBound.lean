import Tablet.Preamble

-- [TABLET NODE: F2NearDiagonalLargeSPowerBound]

open Filter in
theorem F2NearDiagonalLargeSPowerBound (eps : ℝ) (heps : 0 < eps) :
    ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s → (s : ℝ) ≤ Real.rpow 2 (eps * (s : ℝ) / 2) := by
-- BODY
  let c : ℝ := Real.log 2 * eps / 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have htend :
      Tendsto (fun x : ℝ => Real.exp x / x ^ (1 : ℕ)) atTop atTop :=
    Real.tendsto_exp_div_pow_atTop 1
  have hlin : Tendsto (fun s : ℕ => c * (s : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hc
  have hcomp :
      Tendsto (fun s : ℕ => Real.exp (c * (s : ℝ)) / (c * (s : ℝ)) ^ (1 : ℕ))
        atTop atTop := htend.comp hlin
  have hev : ∀ᶠ s : ℕ in atTop,
      (1 / c : ℝ) ≤ Real.exp (c * (s : ℝ)) / (c * (s : ℝ)) ^ (1 : ℕ) :=
    (tendsto_atTop.1 hcomp) (1 / c)
  rcases eventually_atTop.1 hev with ⟨N, hN⟩
  refine ⟨N + 1, ?_⟩
  intro s hs
  have hsN : N ≤ s := by omega
  have hspos_nat : 0 < s := by omega
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hspos_nat
  have hdenpos : 0 < c * (s : ℝ) := mul_pos hc hspos
  have hratio := hN s hsN
  have hm :=
      mul_le_mul_of_nonneg_right hratio hdenpos.le
  have hexp : (s : ℝ) ≤ Real.exp (c * (s : ℝ)) := by
    calc
      (s : ℝ) = (1 / c) * (c * (s : ℝ)) := by
        field_simp [hc.ne']
      _ ≤ (Real.exp (c * (s : ℝ)) / (c * (s : ℝ)) ^ (1 : ℕ)) *
            (c * (s : ℝ)) := hm
      _ = Real.exp (c * (s : ℝ)) := by
        norm_num
        field_simp [hdenpos.ne']
  have hrpow : Real.rpow 2 (eps * (s : ℝ) / 2) = Real.exp (c * (s : ℝ)) := by
    change (2 : ℝ) ^ (eps * (s : ℝ) / 2) = Real.exp (c * (s : ℝ))
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    dsimp [c]
    ring_nf
  rw [hrpow]
  exact hexp
