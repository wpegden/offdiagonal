import Tablet.RamseyNumberPositive

-- [TABLET NODE: MainTheoremFiniteAbsorption]

theorem MainTheoremFiniteAbsorption (s k0 : ℕ) (C : ℝ)
    (hs : 4 ≤ s) (hC : 0 < C)
    (hlarge : ∀ k : ℕ, k0 ≤ k → 2 ≤ k →
      C * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤
        (RamseyNumber s k : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      c * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  classical
  let T : ℕ → ℝ := fun k =>
    ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))
  have hT_pos : ∀ k : ℕ, 2 ≤ k → 0 < T k := by
    intro k hk2
    have hkpos_nat : 0 < k := by omega
    have hkgt1_nat : 1 < k := by omega
    have hkpos : 0 < (k : ℝ) := by exact_mod_cast hkpos_nat
    have hkgt1 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hkgt1_nat
    have hlogpos : 0 < Real.log (k : ℝ) := Real.log_pos hkgt1
    dsimp [T]
    positivity
  let small : Finset ℕ := (Finset.range k0).filter (fun k => 2 ≤ k)
  by_cases hsmall : small.Nonempty
  · let ratio : ℕ → ℝ := fun k => (RamseyNumber s k : ℝ) / T k
    rcases Finset.exists_min_image small ratio hsmall with
      ⟨kmin, hkmin_mem, hkmin_le⟩
    have hkmin2 : 2 ≤ kmin := by
      exact (Finset.mem_filter.mp hkmin_mem).2
    have hratio_pos : 0 < ratio kmin := by
      have hram_pos : 0 < (RamseyNumber s kmin : ℝ) := by
        exact_mod_cast RamseyNumberPositive s kmin (by omega) (by omega)
      have hTk_pos : 0 < T kmin := hT_pos kmin hkmin2
      change 0 < (RamseyNumber s kmin : ℝ) / T kmin
      exact div_pos hram_pos hTk_pos
    let c : ℝ := min C (ratio kmin)
    have hc_pos : 0 < c := lt_min hC hratio_pos
    refine ⟨c, hc_pos, ?_⟩
    intro k hk2
    by_cases hklarge : k0 ≤ k
    · have hc_le_C : c ≤ C := min_le_left C (ratio kmin)
      have hlarge_k := hlarge k hklarge hk2
      have hT_nonneg : 0 ≤ T k := (hT_pos k hk2).le
      have hmul_le_large : c * T k ≤ C * T k :=
        mul_le_mul_of_nonneg_right hc_le_C hT_nonneg
      calc
        c * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))
            = c * T k := by
              dsimp [T]
              ring
        _ ≤ C * T k := hmul_le_large
        _ = C * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) := by
              dsimp [T]
              ring
        _ ≤ (RamseyNumber s k : ℝ) := hlarge_k
    · have hklt : k < k0 := Nat.lt_of_not_ge hklarge
      have hkmem : k ∈ small := by
        simp [small, hklt, hk2]
      have hratio_le : ratio kmin ≤ ratio k := hkmin_le k hkmem
      have hc_le_ratio : c ≤ ratio k := (min_le_right C (ratio kmin)).trans hratio_le
      have hTk_pos : 0 < T k := hT_pos k hk2
      have hmul_le : c * T k ≤ (RamseyNumber s k : ℝ) := by
        calc
          c * T k ≤ ratio k * T k :=
            mul_le_mul_of_nonneg_right hc_le_ratio hTk_pos.le
          _ = (RamseyNumber s k : ℝ) := by
            change ((RamseyNumber s k : ℝ) / T k) * T k = (RamseyNumber s k : ℝ)
            field_simp [ne_of_gt hTk_pos]
      calc
        c * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6))
            = c * T k := by
              dsimp [T]
              ring
        _ ≤ (RamseyNumber s k : ℝ) := hmul_le
  · refine ⟨C, hC, ?_⟩
    intro k hk2
    by_cases hklarge : k0 ≤ k
    · exact hlarge k hklarge hk2
    · have hklt : k < k0 := Nat.lt_of_not_ge hklarge
      have hkmem : k ∈ small := by
        simp [small, hklt, hk2]
      exact False.elim (hsmall ⟨k, hkmem⟩)
