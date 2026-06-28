import Tablet.BinarySequenceWeight

-- [TABLET NODE: MarkedTreePathCounting]

universe u

theorem MarkedTreePathCounting {P : Type u} [Fintype P]
    (k w Delta h : ℕ) (signature : P → Fin k → Bool)
    (hk : w ≤ k) (hhDelta : h ≤ Delta)
    (hpath : ∀ p : P, BinarySequenceWeight (signature p) ≤ w)
    (hfiber : ∀ z : Fin k → Bool,
      Fintype.card {p : P // signature p = z} ≤
        Delta ^ BinarySequenceWeight z * h ^ (k - BinarySequenceWeight z)) :
    Fintype.card P ≤ 2 ^ k * Delta ^ w * h ^ (k - w) := by
-- BODY
  sorry
