import Tablet.F2BadTupleRankAmbientBound
import Tablet.F2BadTupleRankIncreaseSet
import Tablet.F2BadTupleRankOne
import Tablet.F2BadTupleRankStep
import Tablet.F2BadTupleRankZero

-- [TABLET NODE: F2BadTupleRankIncreaseSetCard]

theorem F2BadTupleRankIncreaseSetCard (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    (hbad : F2BadTuple p k ab) (hk : 0 < k) :
    F2BadTupleRank p k ab k ∈ Finset.Icc 1 p ∧
      (F2BadTupleRankIncreaseSet p k ab).card = F2BadTupleRank p k ab k := by
-- BODY
  classical
  let r : ℕ → ℕ := fun n => F2BadTupleRank p k ab n
  let incNat : ℕ → Finset ℕ :=
    fun n => (Finset.range n).filter (fun m => r (m + 1) = r m + 1)
  have hcard_range : ∀ n : ℕ, n ≤ k → (incNat n).card = r n := by
    intro n hn
    induction n with
    | zero =>
        simp [incNat, r, F2BadTupleRankZero]
    | succ n ih =>
        have hnlt : n < k := Nat.succ_le_iff.mp hn
        have ihn : n ≤ k := Nat.le_of_succ_le hn
        have ih' := ih ihn
        have hstep : r (n + 1) = r n ∨ r (n + 1) = r n + 1 := by
          exact F2BadTupleRankStep p k ab hnlt
        by_cases hinc : r (n + 1) = r n + 1
        · have hn_not : n ∉ incNat n := by
            simp [incNat]
          have hsucc : incNat (n + 1) = insert n (incNat n) := by
            ext m
            by_cases hm : m = n
            · subst m
              simp [incNat, hinc]
            · simp [incNat, Finset.range_add_one, hm]
          rw [hsucc, Finset.card_insert_of_notMem hn_not, ih', hinc]
        · have hsame : r (n + 1) = r n := by
            cases hstep with
            | inl h => exact h
            | inr h => exact (hinc h).elim
          have hsucc : incNat (n + 1) = incNat n := by
            ext m
            by_cases hm : m = n
            · subst m
              simp [incNat, hinc]
            · simp [incNat, Finset.range_add_one, hm]
          rw [hsucc, ih', hsame]
  have hmap :
      (F2BadTupleRankIncreaseSet p k ab).map Fin.valEmbedding = incNat k := by
    ext n
    constructor
    · intro hn
      rcases Finset.mem_map.mp hn with ⟨j, hj, hval⟩
      have hpred : r (j.val + 1) = r j.val + 1 := by
        simpa [F2BadTupleRankIncreaseSet, r] using hj
      have hnval : n = j.val := by
        simpa using hval.symm
      have hnlt : n < k := by omega
      have hp : r (n + 1) = r n + 1 := by
        simpa [hnval] using hpred
      exact by simp [incNat, hnlt, hp]
    · intro hn
      have hn' : n < k ∧ r (n + 1) = r n + 1 := by
        simpa [incNat] using hn
      rcases hn' with ⟨hnlt, hpred⟩
      let j : Fin k := ⟨n, hnlt⟩
      apply Finset.mem_map.mpr
      refine ⟨j, ?_, ?_⟩
      · simpa [F2BadTupleRankIncreaseSet, j, r] using hpred
      · rfl
  have hcard_set :
      (F2BadTupleRankIncreaseSet p k ab).card = r k := by
    have hcard_map :
        ((F2BadTupleRankIncreaseSet p k ab).map Fin.valEmbedding).card =
          (F2BadTupleRankIncreaseSet p k ab).card := by
      exact Finset.card_map (s := F2BadTupleRankIncreaseSet p k ab) Fin.valEmbedding
    rw [← hcard_map, hmap, hcard_range k le_rfl]
  have hupper : r k ≤ p := by
    exact F2BadTupleRankAmbientBound p k ab k
  let i0 : Fin k := ⟨0, hk⟩
  have hmem0 : i0 ∈ F2BadTupleRankIncreaseSet p k ab := by
    simp [F2BadTupleRankIncreaseSet, i0, F2BadTupleRankZero,
      F2BadTupleRankOne p k ab hbad hk]
  have hpos_card : 0 < (F2BadTupleRankIncreaseSet p k ab).card := by
    exact Finset.card_pos.mpr ⟨i0, hmem0⟩
  have hlower : 1 ≤ r k := by omega
  constructor
  · simp [Finset.mem_Icc, r, hlower, hupper]
  · exact hcard_set
