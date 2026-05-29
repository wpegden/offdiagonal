import Tablet.Preamble

-- [TABLET NODE: BinarySequenceWeight]

noncomputable def BinarySequenceWeight {t : ℕ} (z : Fin t → Bool) : ℕ := by
-- BODY
  classical
  exact (Finset.univ.filter (fun i : Fin t => z i = true)).card
