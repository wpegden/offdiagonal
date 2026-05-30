import Tablet.RamseyNumber
import Tablet.RamseyPropertyCounterexampleTransport
import Tablet.RamseyPropertyMonotone
import Tablet.RamseyPropertyNonempty

-- [TABLET NODE: RamseyNumberLowerBoundFromCounterexample]

universe u

theorem RamseyNumberLowerBoundFromCounterexample {W : Type u} [Fintype W]
    (H : SimpleGraph W) (s k : ℕ)
    (hNoClique : ¬ ∃ S : Finset W, H.IsNClique s S)
    (hNoIndependent : ¬ ∃ I : Finset W, Hᶜ.IsNClique k I) :
    Fintype.card W < RamseyNumber s k := by
-- BODY
  classical
  have hnot : ¬ RamseyProperty s k (Fintype.card W) :=
    RamseyPropertyCounterexampleTransport H s k hNoClique hNoIndependent
  unfold RamseyNumber
  by_contra hlt
  have hle : sInf {n : ℕ | RamseyProperty s k n} ≤ Fintype.card W :=
    Nat.le_of_not_gt hlt
  have hmin_mem : RamseyProperty s k (sInf {n : ℕ | RamseyProperty s k n}) :=
    Nat.sInf_mem (RamseyPropertyNonempty s k)
  exact hnot (RamseyPropertyMonotone s k
    (sInf {n : ℕ | RamseyProperty s k n}) (Fintype.card W) hle hmin_mem)
