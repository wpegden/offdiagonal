import Tablet.F2ForwardIndependentTuples
import Tablet.F2ForwardIndependentSumBound

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
  classical
  intro C hC
  refine ⟨4, ?_⟩
  intro s hs
  let k : ℕ := Nat.ceil (C * (s : ℝ))
  have hs4 : 4 ≤ s := hs
  have hsk : s ≤ k := by
    have hreal : (s : ℝ) ≤ C * (s : ℝ) := by
      have hC_le : (1 : ℝ) ≤ C := le_of_lt hC
      calc
        (s : ℝ) = 1 * (s : ℝ) := by ring
        _ ≤ C * (s : ℝ) :=
          mul_le_mul_of_nonneg_right hC_le (by positivity : 0 ≤ (s : ℝ))
    have hceil := Nat.ceil_mono hreal
    simpa [k, Nat.ceil_natCast] using hceil
  rcases F2ForwardIndependentTuples s k hs4 hsk with
    ⟨W, hW, D, hloop, hfree, hcard, hcount⟩
  refine ⟨W, hW, D, hloop, hfree, hcard, ?_⟩
  have hsum := F2ForwardIndependentSumBound s k hs4 hsk
  simpa [k] using le_trans hcount hsum
