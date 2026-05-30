import Tablet.RamseyNumber
import Tablet.RamseyPropertyNonempty

-- [TABLET NODE: RamseyNumberPositive]

theorem RamseyNumberPositive (s k : ℕ) (hs : 0 < s) (hk : 0 < k) :
    0 < RamseyNumber s k := by
-- BODY
  classical
  have hnot : ¬ RamseyProperty s k 0 := by
    intro h
    rcases h (⊥ : SimpleGraph (Fin 0)) with hclique | hind
    · rcases hclique with ⟨S, hS⟩
      have hcard0 : S.card = 0 := by
        have hSempty : S = ∅ := by
          ext x
          exact Fin.elim0 x
        simp [hSempty]
      have hcards : S.card = s := hS.card_eq
      omega
    · rcases hind with ⟨I, hI⟩
      have hcard0 : I.card = 0 := by
        have hIempty : I = ∅ := by
          ext x
          exact Fin.elim0 x
        simp [hIempty]
      have hcardk : I.card = k := hI.card_eq
      omega
  unfold RamseyNumber
  by_contra hpos
  have hzero : sInf {n : ℕ | RamseyProperty s k n} = 0 :=
    Nat.eq_zero_of_not_pos hpos
  have hmin_mem : RamseyProperty s k (sInf {n : ℕ | RamseyProperty s k n}) :=
    Nat.sInf_mem (RamseyPropertyNonempty s k)
  exact hnot (by simpa [hzero] using hmin_mem)
