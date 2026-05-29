import Tablet.MulticolorRamseyProperty

-- [TABLET NODE: MulticolorRamseyNumber]

noncomputable def MulticolorRamseyNumber (s ell : ℕ) : ℕ :=
-- BODY
  sInf {n : ℕ | MulticolorRamseyProperty s ell n}
