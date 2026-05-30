import Tablet.F2ForwardIndependentTuples
import Tablet.F2NearDiagonalExponentIdentity
import Tablet.F2NearDiagonalChooseSymmetry
import Tablet.F2NearDiagonalLargeSPowerBound
import Tablet.F2NearDiagonalQuadraticMaxBound
import Tablet.F2NearDiagonalSummationAbsorptionBound
import Tablet.F2NearDiagonalSummandFromLogControls
import Tablet.F2NearDiagonalLogControlBundle

-- [TABLET NODE: F2ForwardIndependentNearDiagonalBound]

theorem F2ForwardIndependentNearDiagonalBound :
    ∀ eps : ℝ, 0 < eps → ∃ delta : ℝ, 0 < delta ∧ ∃ s0 : ℕ,
      ∀ s a : ℕ, s0 ≤ s → (a : ℝ) ≤ delta * (s : ℝ) →
        ∃ (W : Type) (_ : Fintype W), ∃ D : Digraph W,
          DigraphLoopless D ∧
            TransitiveTournamentFree D s ∧
              Fintype.card W = 2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 ∧
                ((ForwardIndependentTupleCount D (s + a) : ℕ) : ℝ) ≤
                  Real.rpow 2
                    ((3 / 2 : ℝ) * (s : ℝ) ^ 2 + (a : ℝ) * (s : ℝ) -
                      (5 / 2 : ℝ) * (s : ℝ) + eps * (s : ℝ)) := by
-- BODY
  intro eps heps
  rcases F2NearDiagonalLogControlBundle eps heps with
    ⟨delta, hdelta_pos, sBundle, hbundle⟩
  rcases F2NearDiagonalLargeSPowerBound eps heps with ⟨sPow, hpow⟩
  refine ⟨delta, hdelta_pos, max (max sBundle sPow) 4, ?_⟩
  intro s a hs ha
  have hsBundle : sBundle ≤ s :=
    le_trans (Nat.le_max_left sBundle sPow)
      (le_trans (Nat.le_max_left (max sBundle sPow) 4) hs)
  have hsPow : sPow ≤ s :=
    le_trans (Nat.le_max_right sBundle sPow)
      (le_trans (Nat.le_max_left (max sBundle sPow) 4) hs)
  have hs4 : 4 ≤ s :=
    le_trans (Nat.le_max_right (max sBundle sPow) 4) hs
  rcases F2ForwardIndependentTuples s (s + a) hs4 (by omega : s ≤ s + a) with
    ⟨W, instW, D, hloopless, hfree, hcard, hsum⟩
  letI : Fintype W := instW
  refine ⟨W, instW, D, hloopless, hfree, ?_, ?_⟩
  · simpa using hcard
  · have hs_pow := hpow s hsPow
    have hterm :
        ∀ t ∈ Finset.Icc 1 (s - 1),
          ((Nat.choose (s + a) t : ℕ) : ℝ) *
              Real.rpow 2
                ((((s - 1) * (t + (s + a)) - Nat.choose (t + 1) 2 : ℕ) : ℝ)) ≤
            Real.rpow 2
              ((s : ℝ) ^ 2 / 2 + (s : ℝ) * ((s + a : ℕ) : ℝ) -
                (3 / 2 : ℝ) * (s : ℝ) - ((s + a : ℕ) : ℝ) +
                  eps * (s : ℝ) / 2) := by
      intro t ht
      rcases hbundle s a t hsBundle ha ht with ⟨lambda, hchoose, ha_control, hj_control⟩
      exact F2NearDiagonalSummandFromLogControls eps lambda s a t ht hchoose ha_control hj_control
    have hsum_bound := F2NearDiagonalSummationAbsorptionBound eps s a hs_pow hterm
    exact hsum.trans hsum_bound
