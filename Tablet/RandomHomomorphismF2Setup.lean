import Tablet.F2ForwardIndependentNearDiagonalBound

-- [TABLET NODE: RandomHomomorphismF2Setup]

theorem RandomHomomorphismF2Setup :
    ∃ s0 : ℕ, 4 ≤ s0 ∧ ∀ s : ℕ, s0 ≤ s →
      ∃ (W : Type) (_ : Fintype W), ∃ D : Digraph W,
        DigraphLoopless D ∧
          TransitiveTournamentFree D s ∧
            Fintype.card W = 2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 ∧
              ((2 ^ (2 * s - 4) : ℕ) : ℝ) < (Fintype.card W : ℝ) ∧
                ((ForwardIndependentTupleCount D s : ℕ) : ℝ) ≤
                  Real.rpow 2 ((3 / 2 : ℝ) * (s : ℝ) ^ 2) := by
-- BODY
  rcases F2ForwardIndependentNearDiagonalBound 1 (by norm_num) with
    ⟨delta, hdelta_pos, sF, hF⟩
  refine ⟨max sF 4, Nat.le_max_right sF 4, ?_⟩
  intro s hs
  have hsF : sF ≤ s := le_trans (Nat.le_max_left sF 4) hs
  have hs4 : 4 ≤ s := le_trans (Nat.le_max_right sF 4) hs
  have ha : ((0 : ℕ) : ℝ) ≤ delta * (s : ℝ) := by
    simpa using (mul_nonneg hdelta_pos.le (by positivity : 0 ≤ (s : ℝ)))
  rcases hF s 0 hsF ha with ⟨W, instW, D, hloopless, hfree, hcard, hcount⟩
  refine ⟨W, instW, D, hloopless, hfree, hcard, ?_, ?_⟩
  · rw [hcard]
    have hA_eq : 2 ^ (2 * s - 4) = (2 ^ (s - 2)) * (2 ^ (s - 2)) := by
      rw [← pow_add]
      congr
      omega
    have hA_ge_3B : 3 * 2 ^ (s - 2) ≤ 2 ^ (2 * s - 4) := by
      rw [hA_eq]
      have hB_ge3 : 3 ≤ 2 ^ (s - 2) := by
        exact le_trans (by norm_num : 3 ≤ 4)
          (Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) (by omega : 2 ≤ s - 2))
      nlinarith
    have hsmall :
        2 ^ (s - 1) + 2 ^ (s - 2) ≤ 2 ^ (2 * s - 4) := by
      have hsucc : s - 1 = (s - 2) + 1 := by omega
      rw [hsucc, pow_add]
      norm_num
      nlinarith [hA_ge_3B]
    have hbig_eq : 2 ^ (2 * s - 3) = 2 * 2 ^ (2 * s - 4) := by
      have hsucc : 2 * s - 3 = (2 * s - 4) + 1 := by omega
      rw [hsucc, pow_add]
      ring
    have hNgt_nat :
        2 ^ (2 * s - 4) <
          2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 := by
      rw [hbig_eq]
      omega
    exact_mod_cast hNgt_nat
  · have hexp_le :
        (3 / 2 : ℝ) * (s : ℝ) ^ 2 + ((0 : ℕ) : ℝ) * (s : ℝ) -
            (5 / 2 : ℝ) * (s : ℝ) + (1 : ℝ) * (s : ℝ) ≤
          (3 / 2 : ℝ) * (s : ℝ) ^ 2 := by
      nlinarith [show (0 : ℝ) ≤ (s : ℝ) by positivity]
    exact hcount.trans
      (Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_le)
