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
  sorry
