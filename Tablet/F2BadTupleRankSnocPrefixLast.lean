import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleRankSnocPrefixLast]

theorem F2BadTupleRankSnocPrefixLast (p m : ℕ)
    (ab : Fin (m + 1) → (Fin p → ZMod 2) × (Fin p → ZMod 2)) :
    F2BadTupleRank p (m + 1)
        (@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
          (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0))
        (m + 1) =
      F2BadTupleRank p (m + 1) ab (m + 1) := by
-- BODY
  unfold F2BadTupleRank
  have hset :
      Set.range
          (fun j : {j : Fin (m + 1) // j.val < m + 1} =>
            ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
              (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0)) j.1).1)
        =
      Set.range
          (fun j : {j : Fin (m + 1) // j.val < m + 1} => (ab j.1).1) := by
    ext v
    constructor
    · intro hv
      rcases hv with ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      by_cases hlast : j.1 = Fin.last m
      · change
          (ab j.1).1 =
            ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
              (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0)) j.1).1
        rw [hlast]
        simp
      · have hlt : j.1.val < m := by
          have hne : j.1.val ≠ m := by
            intro hval
            apply hlast
            apply Fin.ext
            simpa using hval
          omega
        let jj : Fin m := ⟨j.1.val, hlt⟩
        have hjj : jj.castSucc = j.1 := by
          apply Fin.ext
          rfl
        change
          (ab j.1).1 =
            ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
              (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0)) j.1).1
        calc
          (ab j.1).1 = (ab jj.castSucc).1 := by rw [hjj]
          _ =
              ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0))
                jj.castSucc).1 := by
              simp
          _ =
              ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0))
                j.1).1 := by
              rw [hjj]
    · intro hv
      rcases hv with ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      by_cases hlast : j.1 = Fin.last m
      · change
          ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
            (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0)) j.1).1 =
            (ab j.1).1
        rw [hlast]
        simp
      · have hlt : j.1.val < m := by
          have hne : j.1.val ≠ m := by
            intro hval
            apply hlast
            apply Fin.ext
            simpa using hval
          omega
        let jj : Fin m := ⟨j.1.val, hlt⟩
        have hjj : jj.castSucc = j.1 := by
          apply Fin.ext
          rfl
        change
          ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
            (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0)) j.1).1 =
            (ab j.1).1
        calc
          ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
            (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0)) j.1).1 =
              ((@Fin.snoc m (fun _ => (Fin p → ZMod 2) × (Fin p → ZMod 2))
                (fun i : Fin m => ab i.castSucc) ((ab (Fin.last m)).1, 0))
                jj.castSucc).1 := by
              rw [hjj]
          _ = (ab jj.castSucc).1 := by
              simp
          _ = (ab j.1).1 := by
              rw [hjj]
  rw [hset]
