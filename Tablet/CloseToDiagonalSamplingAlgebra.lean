import Tablet.Preamble

-- [TABLET NODE: CloseToDiagonalSamplingAlgebra]

theorem CloseToDiagonalSamplingAlgebra (k : ℕ) (E I F : ℝ) (hk : 1 ≤ k)
    (hI_bound : I ≤ (Real.exp 1 / (k : ℝ)) ^ k * F)
    (hF_bound : F ≤ Real.rpow 2 E)
    (hI_pos : 1 ≤ I) :
    let p0 : ℝ := ((k : ℝ) / Real.exp 1) * Real.rpow 2 (-(E / (k : ℝ)))
    Real.rpow p0 (k : ℝ) * I ≤ 1 ∧ p0 ≤ 1 := by
-- BODY
  intro p0
  have hk_pos_nat : 0 < k := by omega
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
  have hA_pos : 0 < (k : ℝ) / Real.exp 1 := by positivity
  have hB_pos : 0 < Real.rpow 2 (-(E / (k : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hp0_pos : 0 < p0 := by
    dsimp [p0]
    positivity
  have hp0_pow_nonneg : 0 ≤ Real.rpow p0 (k : ℝ) :=
    (Real.rpow_pos_of_pos hp0_pos (k : ℝ)).le
  have hp0_pow_eq :
      Real.rpow p0 (k : ℝ) =
        (((k : ℝ) / Real.exp 1) ^ k) * Real.rpow 2 (-E) := by
    have hA_nat :
        Real.rpow ((k : ℝ) / Real.exp 1) (k : ℝ) =
          (((k : ℝ) / Real.exp 1) ^ k) := by
      change ((k : ℝ) / Real.exp 1) ^ (k : ℝ) =
        (((k : ℝ) / Real.exp 1) ^ k)
      rw [Real.rpow_natCast]
    have hB_mul :
        Real.rpow (Real.rpow 2 (-(E / (k : ℝ)))) (k : ℝ) =
          Real.rpow 2 ((-(E / (k : ℝ))) * (k : ℝ)) := by
      change ((2 : ℝ) ^ (-(E / (k : ℝ)))) ^ (k : ℝ) =
        (2 : ℝ) ^ ((-(E / (k : ℝ))) * (k : ℝ))
      rw [Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    dsimp [p0]
    calc
      Real.rpow (((k : ℝ) / Real.exp 1) *
          Real.rpow 2 (-(E / (k : ℝ)))) (k : ℝ)
          = Real.rpow ((k : ℝ) / Real.exp 1) (k : ℝ) *
              Real.rpow (Real.rpow 2 (-(E / (k : ℝ)))) (k : ℝ) := by
              exact Real.mul_rpow hA_pos.le hB_pos.le
      _ = (((k : ℝ) / Real.exp 1) ^ k) *
              Real.rpow 2 ((-(E / (k : ℝ))) * (k : ℝ)) := by
              rw [hA_nat, hB_mul]
      _ = (((k : ℝ) / Real.exp 1) ^ k) * Real.rpow 2 (-E) := by
              congr 1
              field_simp [hkR_ne]
  have hsampling_count : Real.rpow p0 (k : ℝ) * I ≤ 1 := by
    have hcoef_nonneg :
        0 ≤ Real.rpow p0 (k : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k := by
      positivity
    calc
      Real.rpow p0 (k : ℝ) * I
          ≤ Real.rpow p0 (k : ℝ) *
              ((Real.exp 1 / (k : ℝ)) ^ k * F) := by
              exact mul_le_mul_of_nonneg_left hI_bound hp0_pow_nonneg
      _ = (Real.rpow p0 (k : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k) * F := by ring
      _ ≤ (Real.rpow p0 (k : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k) *
              Real.rpow 2 E := by
              exact mul_le_mul_of_nonneg_left hF_bound hcoef_nonneg
      _ = 1 := by
              rw [hp0_pow_eq]
              have hpow_cancel :
                  (((k : ℝ) / Real.exp 1) ^ k) *
                    (Real.exp 1 / (k : ℝ)) ^ k = 1 := by
                    rw [← mul_pow]
                    field_simp [hkR_ne, (Real.exp_pos 1).ne']
                    norm_num
              have hrpow_cancel : Real.rpow 2 (-E) * Real.rpow 2 E = 1 := by
                change (2 : ℝ) ^ (-E) * (2 : ℝ) ^ E = 1
                rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
                ring_nf
                norm_num
              calc
                (((k : ℝ) / Real.exp 1) ^ k * Real.rpow 2 (-E)) *
                    (Real.exp 1 / (k : ℝ)) ^ k * Real.rpow 2 E
                    = ((((k : ℝ) / Real.exp 1) ^ k) *
                        (Real.exp 1 / (k : ℝ)) ^ k) *
                        (Real.rpow 2 (-E) * Real.rpow 2 E) := by ring
                _ = 1 := by rw [hpow_cancel, hrpow_cancel]; ring
  have hp0_pow_le_one : Real.rpow p0 (k : ℝ) ≤ 1 := by
    have hle_mul : Real.rpow p0 (k : ℝ) ≤ Real.rpow p0 (k : ℝ) * I := by
      nlinarith
    exact hle_mul.trans hsampling_count
  have hp0_le_one : p0 ≤ 1 := by
    by_contra hnot
    have hp0_gt_one : 1 < p0 := lt_of_not_ge hnot
    have hpow_gt_one : 1 < Real.rpow p0 (k : ℝ) :=
      Real.one_lt_rpow hp0_gt_one hkR_pos
    linarith
  exact ⟨hsampling_count, hp0_le_one⟩
