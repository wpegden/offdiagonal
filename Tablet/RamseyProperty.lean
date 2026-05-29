import Tablet.Preamble

-- [TABLET NODE: RamseyProperty]

def RamseyProperty (s k n : ℕ) : Prop :=
-- BODY
  ∀ G : SimpleGraph (Fin n),
    (∃ S : Finset (Fin n), G.IsNClique s S) ∨
      (∃ I : Finset (Fin n), Gᶜ.IsNClique k I)
