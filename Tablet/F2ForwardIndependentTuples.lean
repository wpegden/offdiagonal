import Tablet.DigraphLoopless
import Tablet.ForwardIndependentTupleCount
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: F2ForwardIndependentTuples]

universe u

theorem F2ForwardIndependentTuples :
    ∀ s k : ℕ, 4 ≤ s → s ≤ k →
      ∃ (W : Type) (_ : Fintype W), ∃ D : Digraph W,
        DigraphLoopless D ∧
          TransitiveTournamentFree D s ∧
            Fintype.card W = 2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 ∧
              ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤
                Finset.sum (Finset.Icc 1 (s - 1))
                  (fun t => ((Nat.choose k t : ℕ) : ℝ) *
                    Real.rpow 2
                      ((((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) := by
-- BODY
  sorry
