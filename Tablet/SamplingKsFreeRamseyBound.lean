import Tablet.RamseyNumber
import Tablet.SimpleGraphIndependentSetCount

-- [TABLET NODE: SamplingKsFreeRamseyBound]

universe u

theorem SamplingKsFreeRamseyBound {V : Type u} [Fintype V]
    (G : SimpleGraph V) (s k : ℕ) (p : ℝ)
    (hKs : ¬ ∃ S : Finset V, G.IsNClique s S)
    (hk : 1 ≤ k)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcount : Real.rpow p (k : ℝ) *
      ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) ≤ 1) :
    p * (Fintype.card V : ℝ) - 1 < (RamseyNumber s k : ℝ) := by
-- BODY
  sorry
