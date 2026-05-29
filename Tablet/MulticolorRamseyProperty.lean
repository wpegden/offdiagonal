import Tablet.Preamble

-- [TABLET NODE: MulticolorRamseyProperty]

def MulticolorRamseyProperty (s ell n : ℕ) : Prop :=
-- BODY
  ∀ color : Sym2 (Fin n) → Fin ell,
    ∃ S : Finset (Fin n),
      S.card = s ∧ ∃ c : Fin ell,
        ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v → color (Sym2.mk u v) = c
