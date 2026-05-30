import Tablet.Preamble

-- [TABLET NODE: F2NearDiagonalChooseSymmetry]

theorem F2NearDiagonalChooseSymmetry (s a j : ℕ) (hj : j ≤ s) :
    Nat.choose (s + a) (s - j) = Nat.choose (s + a) (j + a) := by
-- BODY
  have hle : j + a ≤ s + a := by omega
  have hsub : s + a - (j + a) = s - j := by omega
  simpa [hsub] using Nat.choose_symm hle
