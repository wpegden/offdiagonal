import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductMarkedChildrenBound]

theorem StarProductMarkedChildrenBound (q t A popular poor : ℕ)
    (hpopular : popular ≤ 128 * t * q ^ t)
    (hpoor : poor ≤ 10000 * t * q ^ t)
    (hA : 10128 * t ≤ A) :
    popular + poor ≤ A * q ^ t := by
-- BODY
  have hsum : popular + poor ≤ (128 * t + 10000 * t) * q ^ t := by
    nlinarith [hpopular, hpoor]
  have hconst : (128 * t + 10000 * t) * q ^ t = 10128 * t * q ^ t := by
    ring
  have hA' : 10128 * t * q ^ t ≤ A * q ^ t :=
    Nat.mul_le_mul_right (q ^ t) hA
  exact hsum.trans (by simpa [hconst] using hA')
