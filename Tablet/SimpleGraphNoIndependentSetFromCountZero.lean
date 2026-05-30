import Tablet.SimpleGraphIndependentSetCount

-- [TABLET NODE: SimpleGraphNoIndependentSetFromCountZero]

universe u

theorem SimpleGraphNoIndependentSetFromCountZero {V : Type u} [Fintype V]
    (G : SimpleGraph V) (k : ℕ)
    (hzero : SimpleGraphIndependentSetCount G k = 0) :
    ¬ ∃ I : Finset V, Gᶜ.IsNClique k I := by
-- BODY
  classical
  intro hIndependent
  rcases hIndependent with ⟨I, hI⟩
  have hnonempty : Nonempty {S : Finset V // Gᶜ.IsNClique k S} := ⟨⟨I, hI⟩⟩
  have hpos : 0 < SimpleGraphIndependentSetCount G k := by
    simpa [SimpleGraphIndependentSetCount] using Fintype.card_pos_iff.mpr hnonempty
  omega
