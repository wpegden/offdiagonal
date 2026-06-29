import Tablet.RamseyNumberLowerBoundFromCounterexample

-- [TABLET NODE: MainTheoremRamseyPositive]

theorem MainTheoremRamseyPositive (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    0 < RamseyNumber s k := by
-- BODY
  classical
  let H : SimpleGraph (Fin 0) := ⊥
  have hNoClique : ¬ ∃ S : Finset (Fin 0), H.IsNClique s S := by
    rintro ⟨S, hS⟩
    have hcard_zero : S.card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext x
      exact Fin.elim0 x
    have hcard_s : S.card = s := hS.card_eq
    omega
  have hNoIndependent : ¬ ∃ I : Finset (Fin 0), Hᶜ.IsNClique k I := by
    rintro ⟨I, hI⟩
    have hcard_zero : I.card = 0 := by
      apply Finset.card_eq_zero.mpr
      ext x
      exact Fin.elim0 x
    have hcard_k : I.card = k := hI.card_eq
    omega
  have hlt : Fintype.card (Fin 0) < RamseyNumber s k :=
    RamseyNumberLowerBoundFromCounterexample H s k hNoClique hNoIndependent
  simpa using hlt
