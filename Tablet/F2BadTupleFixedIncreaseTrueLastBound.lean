import Tablet.F2BadTupleFixedIncreasePrefixRestriction
import Tablet.F2BadTupleLastPairAmbientFiberBound
import Tablet.F2BadTupleRankIncreaseSetCard
import Tablet.F2BadTupleRankSnocPrefixLast

-- [TABLET NODE: F2BadTupleFixedIncreaseTrueLastBound]

theorem F2BadTupleFixedIncreaseTrueLastBound (p m : ℕ)
    (z : Fin (m + 1) → Bool) (hzlast : z (Fin.last m) = true) :
    F2BadTupleFixedIncreaseCount p (m + 1) z ≤
      F2BadTupleFixedIncreaseCount p m (fun i : Fin m => z i.castSucc) *
        (2 ^ p * 2 ^ (p - BinarySequenceWeight z)) := by
-- BODY
  classical
  have hzlast_true : z (Fin.last m) = true := hzlast
  let Vec : Type := Fin p → ZMod 2
  let zp : Fin m → Bool := fun i => z i.castSucc
  let Full : Type :=
    {ab : Fin (m + 1) → Vec × Vec //
      F2BadTuple p (m + 1) ab ∧
        ∀ i : Fin (m + 1),
          (F2BadTupleRank p (m + 1) ab (i.val + 1) =
              F2BadTupleRank p (m + 1) ab i.val + 1) ↔ z i = true}
  let Pref : Type :=
    {pref : Fin m → Vec × Vec //
      F2BadTuple p m pref ∧
        ∀ i : Fin m,
          (F2BadTupleRank p m pref (i.val + 1) =
              F2BadTupleRank p m pref i.val + 1) ↔ zp i = true}
  let Fiber : Pref → Type := fun pref =>
    {pair : Vec × Vec //
      F2BadTupleRank p (m + 1)
          (@Fin.snoc m (fun _ => Vec × Vec) pref.val (pair.1, 0)) (m + 1) =
          BinarySequenceWeight z ∧
        ∀ j : Fin (m + 1),
          ((@Fin.snoc m (fun _ => Vec × Vec) pref.val (pair.1, 0)) j).1 ⬝ᵥ
            pair.2 = 1}
  change Fintype.card Full ≤
    Fintype.card Pref * (2 ^ p * 2 ^ (p - BinarySequenceWeight z))
  have hfull_rank_weight : ∀ ab : Full,
      F2BadTupleRank p (m + 1) ab.val (m + 1) = BinarySequenceWeight z := by
    intro ab
    have hcard :=
      (F2BadTupleRankIncreaseSetCard p (m + 1) ab.val ab.property.1
        (Nat.succ_pos m)).2
    have hset_card :
        (F2BadTupleRankIncreaseSet p (m + 1) ab.val).card =
          BinarySequenceWeight z := by
      simp [F2BadTupleRankIncreaseSet, BinarySequenceWeight, ab.property.2]
    exact hcard.symm.trans hset_card
  let toSigma : Full → Sigma Fiber := fun ab =>
    let prefVal : Fin m → Vec × Vec := fun i => ab.val i.castSucc
    let prefProp : F2BadTuple p m prefVal ∧
        ∀ i : Fin m,
          (F2BadTupleRank p m prefVal (i.val + 1) =
              F2BadTupleRank p m prefVal i.val + 1) ↔ zp i = true :=
      F2BadTupleFixedIncreasePrefixRestriction p m ab.val z ab.property
    let pref : Pref := ⟨prefVal, prefProp⟩
    let pair : Vec × Vec := ab.val (Fin.last m)
    let pairProp :
        F2BadTupleRank p (m + 1)
            (@Fin.snoc m (fun _ => Vec × Vec) pref.val (pair.1, 0)) (m + 1) =
            BinarySequenceWeight z ∧
          ∀ j : Fin (m + 1),
            ((@Fin.snoc m (fun _ => Vec × Vec) pref.val (pair.1, 0)) j).1 ⬝ᵥ
              pair.2 = 1 := by
      constructor
      · exact (F2BadTupleRankSnocPrefixLast p m ab.val).trans (hfull_rank_weight ab)
      · intro j
        have hbad := ab.property.1 (Fin.last m) j (Fin.le_last j)
        convert hbad using 2
        by_cases hlast : j = Fin.last m
        · rw [hlast]
          simp [pref, prefVal, pair]
        · have hlt : j.val < m := by
            have hne : j.val ≠ m := by
              intro hval
              apply hlast
              apply Fin.ext
              simpa using hval
            omega
          let jj : Fin m := ⟨j.val, hlt⟩
          have hjj : jj.castSucc = j := by
            apply Fin.ext
            rfl
          change
            ((@Fin.snoc m (fun _ => Vec × Vec) pref.val (pair.1, 0)) j).1 =
              (ab.val j).1
          calc
            ((@Fin.snoc m (fun _ => Vec × Vec) pref.val (pair.1, 0)) j).1 =
                ((@Fin.snoc m (fun _ => Vec × Vec) pref.val (pair.1, 0))
                  jj.castSucc).1 := by
                rw [hjj]
            _ = (pref.val jj).1 := by
                simp
            _ = (ab.val jj.castSucc).1 := by
                simp [pref, prefVal]
            _ = (ab.val j).1 := by
                rw [hjj]
    ⟨pref, ⟨pair, pairProp⟩⟩
  have hinj : Function.Injective toSigma := by
    intro ab cd h
    apply Subtype.ext
    funext i
    have hpref : (toSigma ab).1.val = (toSigma cd).1.val := by
      have hfst := congrArg Sigma.fst h
      exact congrArg Subtype.val hfst
    have hpair : ((toSigma ab).2 : Vec × Vec) = ((toSigma cd).2 : Vec × Vec) := by
      exact congrArg (fun s : Sigma Fiber => (s.2 : Vec × Vec)) h
    by_cases hlast : i = Fin.last m
    · rw [hlast]
      exact hpair
    · have hlt : i.val < m := by
        have hne : i.val ≠ m := by
          intro hval
          apply hlast
          apply Fin.ext
          simpa using hval
        omega
      let ii : Fin m := ⟨i.val, hlt⟩
      have hii : ii.castSucc = i := by
        apply Fin.ext
        rfl
      rw [← hii]
      exact congrFun hpref ii
  have hle_sigma : Fintype.card Full ≤ Fintype.card (Sigma Fiber) :=
    Fintype.card_le_of_injective toSigma hinj
  have hcard_sigma :
      Fintype.card (Sigma Fiber) =
        Finset.univ.sum (fun pref : Pref => Fintype.card (Fiber pref)) := by
    simp [Fiber]
  have hfiber_le :
      Finset.univ.sum (fun pref : Pref => Fintype.card (Fiber pref)) ≤
        Finset.univ.sum
          (fun _ : Pref => 2 ^ p * 2 ^ (p - BinarySequenceWeight z)) := by
    refine Finset.sum_le_sum ?_
    intro pref hpref
    simpa [Fiber, Vec] using
      F2BadTupleLastPairAmbientFiberBound p m (BinarySequenceWeight z) pref.val
  have hsum_const :
      Finset.univ.sum
          (fun _ : Pref => 2 ^ p * 2 ^ (p - BinarySequenceWeight z)) =
        Fintype.card Pref * (2 ^ p * 2 ^ (p - BinarySequenceWeight z)) := by
    simp
  have hcounts :
      F2BadTupleFixedIncreaseCount p (m + 1) z = Fintype.card Full := by
    rfl
  have hpref_count :
      F2BadTupleFixedIncreaseCount p m (fun i : Fin m => z i.castSucc) =
        Fintype.card Pref := by
    rfl
  calc
    Fintype.card Full ≤ Fintype.card (Sigma Fiber) := hle_sigma
    _ = Finset.univ.sum (fun pref : Pref => Fintype.card (Fiber pref)) := hcard_sigma
    _ ≤
        Finset.univ.sum
          (fun _ : Pref => 2 ^ p * 2 ^ (p - BinarySequenceWeight z)) := hfiber_le
    _ = Fintype.card Pref * (2 ^ p * 2 ^ (p - BinarySequenceWeight z)) := hsum_const
    _ =
        F2BadTupleFixedIncreaseCount p m (fun i : Fin m => z i.castSucc) *
          (2 ^ p * 2 ^ (p - BinarySequenceWeight z)) := by
        rw [hpref_count]
