import Tablet.F2ForwardIndependentNearDiagonalBound
import Tablet.NoMonochromaticCliqueColoring
import Tablet.RandomHomomorphismColoring
import Tablet.RandomHomomorphismF2Setup
import Tablet.RandomHomomorphismFirstColorOrderedCliqueFree

-- [TABLET NODE: RandomHomomorphismColoringBound]

theorem RandomHomomorphismColoringBound :
    ∀ ell : ℕ, 3 ≤ ell → ∃ s0 : ℕ, ∀ s n : ℕ, s0 ≤ s →
      (n : ℝ) ≤ Real.rpow 2 (((s : ℝ) / 2 - 4) * ((ell - 1 : ℕ) : ℝ)) →
        ∃ color : Sym2 (Fin n) → Fin ell,
          NoMonochromaticCliqueColoring s ell n color := by
-- BODY
  sorry
