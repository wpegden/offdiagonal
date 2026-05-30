import Tablet.ComplementPolarityPairHsFree
import Tablet.LoopGraphComplementNdLambda
import Tablet.MainTheoremEtaBounds
import Tablet.MainTheoremDyadicGaloisScale
import Tablet.MainTheoremFiniteAbsorption
import Tablet.MainTheoremLargeKComparison
import Tablet.MainTheoremPolarityParameterBounds
import Tablet.MainTheoremPolaritySetup
import Tablet.PolarityGraphParameters
import Tablet.RamseyFromGraphPair

-- [TABLET NODE: MainTheorem]

theorem MainTheorem :
    ∀ s : ℕ, 4 ≤ s → ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 2 ≤ k →
      c * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  intro s hs
  have hlarge :
      ∃ k0 : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ k : ℕ, k0 ≤ k → 2 ≤ k →
        C * ((k : ℝ) ^ (s - 2)) / ((Real.log (k : ℝ)) ^ (2 * s - 6)) ≤
          (RamseyNumber s k : ℝ) := by
    rcases MainTheoremDyadicGaloisScale s hs with ⟨kScale, hScale⟩
    sorry
  rcases hlarge with ⟨k0, C, hC, hlarge_bound⟩
  exact MainTheoremFiniteAbsorption s k0 C hs hC hlarge_bound
