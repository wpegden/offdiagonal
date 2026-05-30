import Tablet.MulticolorRamseyNumber
import Tablet.MulticolorRamseyPropertyMonotone
import Tablet.MulticolorRamseyPropertyNonempty
import Tablet.NoMonochromaticCliqueColoring

-- [TABLET NODE: MulticolorRamseyNumberLowerBoundFromCounterexample]

theorem MulticolorRamseyNumberLowerBoundFromCounterexample (s ell n : ℕ)
    (hell : 0 < ell) (color : Sym2 (Fin n) → Fin ell)
    (hNo : NoMonochromaticCliqueColoring s ell n color) :
    n < MulticolorRamseyNumber s ell := by
-- BODY
  classical
  have hnot : ¬ MulticolorRamseyProperty s ell n := by
    intro hprop
    exact hNo (hprop color)
  unfold MulticolorRamseyNumber
  by_contra hlt
  have hle : sInf {m : ℕ | MulticolorRamseyProperty s ell m} ≤ n := Nat.le_of_not_gt hlt
  have hmin_mem :
      MulticolorRamseyProperty s ell (sInf {m : ℕ | MulticolorRamseyProperty s ell m}) :=
    Nat.sInf_mem (MulticolorRamseyPropertyNonempty s ell hell)
  exact hnot (MulticolorRamseyPropertyMonotone s ell
    (sInf {m : ℕ | MulticolorRamseyProperty s ell m}) n hle hmin_mem)

