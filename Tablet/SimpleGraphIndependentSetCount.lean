import Tablet.Preamble

-- [TABLET NODE: SimpleGraphIndependentSetCount]

universe u

noncomputable def SimpleGraphIndependentSetCount {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : ℕ := by
-- BODY
  classical
  letI : DecidablePred (fun S : Finset V => Gᶜ.IsNClique k S) := Classical.decPred _
  exact Fintype.card {S : Finset V // Gᶜ.IsNClique k S}
