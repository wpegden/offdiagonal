import Tablet.F2BadTupleFixedIncreaseFalseExponentBound
import Tablet.F2BadTupleFixedIncreaseFalseLastBound
import Tablet.F2BadTupleFixedIncreaseTrueExponentBound
import Tablet.F2BadTupleFixedIncreaseTrueLastBound

-- [TABLET NODE: F2BadTupleFixedIncreaseCountBound]

theorem F2BadTupleFixedIncreaseCountBound (p k : ℕ) (z : Fin k → Bool)
    (hw : BinarySequenceWeight z ≤ p) :
    F2BadTupleFixedIncreaseCount p k z ≤
      2 ^ (p * (BinarySequenceWeight z + k) - Nat.choose (BinarySequenceWeight z + 1) 2) := by
-- BODY
  classical
  induction k with
  | zero =>
      simp [F2BadTupleFixedIncreaseCount, F2BadTuple, BinarySequenceWeight]
  | succ m ih =>
      let zp : Fin m → Bool := fun i => z i.castSucc
      by_cases hlast_true : z (Fin.last m) = true
      · have hweight : BinarySequenceWeight z = BinarySequenceWeight zp + 1 := by
          simpa [zp, hlast_true] using BinarySequenceWeightSnoc z
        have hzp_le : BinarySequenceWeight zp ≤ p := by
          omega
        have hzp_succ_le : BinarySequenceWeight zp + 1 ≤ p := by
          omega
        have hih := ih zp hzp_le
        have hstep := F2BadTupleFixedIncreaseTrueLastBound p m z hlast_true
        have hcombined :
            F2BadTupleFixedIncreaseCount p (m + 1) z ≤
              2 ^ (p * (BinarySequenceWeight zp + m) -
                  Nat.choose (BinarySequenceWeight zp + 1) 2) *
                (2 ^ p * 2 ^ (p - BinarySequenceWeight z)) := by
          exact le_trans hstep (Nat.mul_le_mul_right _ hih)
        have hfactor :
            2 ^ (p * (BinarySequenceWeight zp + m) -
                  Nat.choose (BinarySequenceWeight zp + 1) 2) *
                (2 ^ p * 2 ^ (p - BinarySequenceWeight z)) ≤
              2 ^ (p * (BinarySequenceWeight z + (m + 1)) -
                  Nat.choose (BinarySequenceWeight z + 1) 2) := by
          rw [hweight]
          exact F2BadTupleFixedIncreaseTrueExponentBound p m
            (BinarySequenceWeight zp) hzp_succ_le
        exact le_trans hcombined hfactor
      · have hlast_false : z (Fin.last m) = false := by
          cases hbit : z (Fin.last m) <;> simp [hbit] at hlast_true ⊢
        have hweight : BinarySequenceWeight z = BinarySequenceWeight zp := by
          simpa [zp, hlast_false] using BinarySequenceWeightSnoc z
        have hzp_le : BinarySequenceWeight zp ≤ p := by
          omega
        have hih := ih zp hzp_le
        have hstep := F2BadTupleFixedIncreaseFalseLastBound p m z hlast_false
        have hcombined :
            F2BadTupleFixedIncreaseCount p (m + 1) z ≤
              2 ^ (p * (BinarySequenceWeight zp + m) -
                  Nat.choose (BinarySequenceWeight zp + 1) 2) *
                (2 ^ BinarySequenceWeight z * 2 ^ (p - BinarySequenceWeight z)) := by
          exact le_trans hstep (Nat.mul_le_mul_right _ hih)
        have hfactor :
            2 ^ (p * (BinarySequenceWeight zp + m) -
                  Nat.choose (BinarySequenceWeight zp + 1) 2) *
                (2 ^ BinarySequenceWeight z * 2 ^ (p - BinarySequenceWeight z)) ≤
              2 ^ (p * (BinarySequenceWeight z + (m + 1)) -
                  Nat.choose (BinarySequenceWeight z + 1) 2) := by
          rw [hweight]
          exact F2BadTupleFixedIncreaseFalseExponentBound p m
            (BinarySequenceWeight zp) hzp_le
        exact le_trans hcombined hfactor
