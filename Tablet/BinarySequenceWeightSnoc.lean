import Tablet.BinarySequenceWeight

-- [TABLET NODE: BinarySequenceWeightSnoc]

theorem BinarySequenceWeightSnoc {t : ℕ} (z : Fin (t + 1) → Bool) :
    BinarySequenceWeight z =
      BinarySequenceWeight (fun i : Fin t => z i.castSucc) +
        (if z (Fin.last t) = true then 1 else 0) := by
-- BODY
  classical
  unfold BinarySequenceWeight
  rw [Finset.card_filter]
  rw [Finset.card_filter]
  rw [Fin.sum_univ_castSucc]

