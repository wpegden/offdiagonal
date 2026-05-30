import Tablet.Preamble

-- [TABLET NODE: F2NearDiagonalQuadraticMaxBound]

theorem F2NearDiagonalQuadraticMaxBound (lambda L y : ℝ) (hlambda : lambda ≤ L)
    (hy : 0 ≤ y) :
    y * lambda + (3 / 2 : ℝ) * y - y ^ 2 / 2 ≤ (L + (3 / 2 : ℝ)) ^ 2 / 2 := by
-- BODY
  have hlin : y * lambda ≤ y * L := mul_le_mul_of_nonneg_left hlambda hy
  have hsquare : 0 ≤ (y - (L + (3 / 2 : ℝ))) ^ 2 := sq_nonneg _
  nlinarith
