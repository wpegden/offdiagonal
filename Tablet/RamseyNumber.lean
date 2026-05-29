import Tablet.RamseyProperty

-- [TABLET NODE: RamseyNumber]

noncomputable def RamseyNumber (s k : ℕ) : ℕ :=
-- BODY
  sInf {n : ℕ | RamseyProperty s k n}
