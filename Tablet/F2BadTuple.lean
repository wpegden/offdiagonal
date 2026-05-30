import Mathlib.Algebra.Field.ZMod
import Tablet.Preamble

-- [TABLET NODE: F2BadTuple]

def F2BadTuple (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) : Prop :=
-- BODY
  ∀ i j : Fin k, j ≤ i → (ab j).1 ⬝ᵥ (ab i).2 = 1
