import Tablet.Preamble

-- [TABLET NODE: NoMonochromaticCliqueColoring]

def NoMonochromaticCliqueColoring (s ell n : ℕ) (color : Sym2 (Fin n) → Fin ell) :
    Prop :=
-- BODY
  ¬ ∃ S : Finset (Fin n),
      S.card = s ∧ ∃ c : Fin ell,
        ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v → color (Sym2.mk u v) = c
