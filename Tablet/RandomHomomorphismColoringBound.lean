import Tablet.F2ForwardIndependentNearDiagonalBound
import Tablet.NoMonochromaticCliqueColoring

-- [TABLET NODE: RandomHomomorphismColoringBound]

theorem RandomHomomorphismColoringBound :
    ∀ ell s n : ℕ, 3 ≤ ell →
      (n : ℝ) ≤ Real.rpow 2 (((s : ℝ) / 2 - 4) * ((ell - 1 : ℕ) : ℝ)) →
        ∃ color : Sym2 (Fin n) → Fin ell,
          NoMonochromaticCliqueColoring s ell n color := by
-- BODY
  sorry
