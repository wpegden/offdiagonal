import Tablet.F2ForwardIndependentTuples

-- [TABLET NODE: F2ForwardIndependentLinearBound]

theorem F2ForwardIndependentLinearBound :
    ∀ C : ℝ, 1 < C → ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      ∃ (W : Type) (_ : Fintype W), ∃ D : Digraph W,
        DigraphLoopless D ∧
          TransitiveTournamentFree D s ∧
            Fintype.card W = 2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 ∧
              ((ForwardIndependentTupleCount D (Nat.ceil (C * (s : ℝ))) : ℕ) : ℝ) ≤
                Real.rpow 2
                  ((s : ℝ) * (Nat.ceil (C * (s : ℝ)) : ℝ) +
                    (s : ℝ) ^ 2 / 2) := by
-- BODY
  sorry
