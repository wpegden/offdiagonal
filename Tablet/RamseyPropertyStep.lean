import Tablet.RamseyProperty

-- [TABLET NODE: RamseyPropertyStep]

theorem RamseyPropertyStep (s k a b : ℕ)
    (ha : RamseyProperty s (k + 1) a)
    (hb : RamseyProperty (s + 1) k b) :
    RamseyProperty (s + 1) (k + 1) (a + b + 1) := by
-- BODY
  classical
  intro G
  let v : Fin (a + b + 1) := 0
  let rest : Finset (Fin (a + b + 1)) := (Finset.univ : Finset (Fin (a + b + 1))).erase v
  let neigh : Finset (Fin (a + b + 1)) := rest.filter (fun w => G.Adj v w)
  let nonneigh : Finset (Fin (a + b + 1)) := rest.filter (fun w => ¬ G.Adj v w)
  by_cases hneigh : a ≤ neigh.card
  · obtain ⟨A, hAsub, hAcard⟩ := Finset.exists_subset_card_eq hneigh
    let Atype := {x : Fin (a + b + 1) // x ∈ A}
    have hAcardType : Fintype.card Atype = Fintype.card (Fin a) := by
      simp [Atype, hAcard]
    let eA : Atype ≃ Fin a := Fintype.equivOfCardEq hAcardType
    let embA : Fin a ↪ Fin (a + b + 1) :=
      { toFun := fun i => (eA.symm i).val
        inj' := by
          intro x y hxy
          apply eA.symm.injective
          exact Subtype.ext hxy }
    let Gsmall : SimpleGraph (Fin a) := SimpleGraph.comap (fun x => embA x) G
    rcases ha Gsmall with hClique | hIndependent
    · rcases hClique with ⟨S, hS⟩
      have hMapped : G.IsNClique s (S.map embA) := by
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.isClique_iff]
          intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hxy' : x' ≠ y' := by
            intro hEq
            exact hxy (by simpa [embA] using congrArg embA hEq)
          have hadj : Gsmall.Adj x' y' := hS.isClique hx' hy' hxy'
          simpa [Gsmall, SimpleGraph.comap_adj, embA] using hadj
        · simpa [embA] using (Finset.card_map embA (s := S)).trans hS.card_eq
      have hv_adj : ∀ w ∈ S.map embA, G.Adj v w := by
        intro w hw
        rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
        have hxA : embA x ∈ A := (eA.symm x).property
        have hxneigh : embA x ∈ neigh := hAsub hxA
        exact (Finset.mem_filter.mp hxneigh).2
      left
      exact ⟨insert v (S.map embA), hMapped.insert hv_adj⟩
    · rcases hIndependent with ⟨I, hI⟩
      have hMapped : Gᶜ.IsNClique (k + 1) (I.map embA) := by
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.isClique_iff]
          intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hxy' : x' ≠ y' := by
            intro hEq
            exact hxy (by simpa [embA] using congrArg embA hEq)
          have hcomp : Gsmallᶜ.Adj x' y' := hI.isClique hx' hy' hxy'
          refine ⟨?_, ?_⟩
          · exact hxy
          · intro hG
            exact hcomp.2 (by
              simpa [Gsmall, SimpleGraph.comap_adj, embA] using hG)
        · simpa [embA] using (Finset.card_map embA (s := I)).trans hI.card_eq
      right
      exact ⟨I.map embA, hMapped⟩
  · have hsplit : neigh.card + nonneigh.card = rest.card := by
      dsimp [neigh, nonneigh]
      rw [Finset.card_filter_add_card_filter_not]
    have hrest : rest.card = a + b := by
      dsimp [rest, v]
      rw [Finset.card_erase_of_mem]
      · simp
      · simp
    have hb_non : b ≤ nonneigh.card := by
      have hlt : neigh.card < a := Nat.lt_of_not_ge hneigh
      omega
    obtain ⟨B, hBsub, hBcard⟩ := Finset.exists_subset_card_eq hb_non
    let Btype := {x : Fin (a + b + 1) // x ∈ B}
    have hBcardType : Fintype.card Btype = Fintype.card (Fin b) := by
      simp [Btype, hBcard]
    let eB : Btype ≃ Fin b := Fintype.equivOfCardEq hBcardType
    let embB : Fin b ↪ Fin (a + b + 1) :=
      { toFun := fun i => (eB.symm i).val
        inj' := by
          intro x y hxy
          apply eB.symm.injective
          exact Subtype.ext hxy }
    let Gsmall : SimpleGraph (Fin b) := SimpleGraph.comap (fun x => embB x) G
    rcases hb Gsmall with hClique | hIndependent
    · rcases hClique with ⟨S, hS⟩
      have hMapped : G.IsNClique (s + 1) (S.map embB) := by
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.isClique_iff]
          intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hxy' : x' ≠ y' := by
            intro hEq
            exact hxy (by simpa [embB] using congrArg embB hEq)
          have hadj : Gsmall.Adj x' y' := hS.isClique hx' hy' hxy'
          simpa [Gsmall, SimpleGraph.comap_adj, embB] using hadj
        · simpa [embB] using (Finset.card_map embB (s := S)).trans hS.card_eq
      left
      exact ⟨S.map embB, hMapped⟩
    · rcases hIndependent with ⟨I, hI⟩
      have hMapped : Gᶜ.IsNClique k (I.map embB) := by
        refine ⟨?_, ?_⟩
        · rw [SimpleGraph.isClique_iff]
          intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hxy' : x' ≠ y' := by
            intro hEq
            exact hxy (by simpa [embB] using congrArg embB hEq)
          have hcomp : Gsmallᶜ.Adj x' y' := hI.isClique hx' hy' hxy'
          refine ⟨?_, ?_⟩
          · exact hxy
          · intro hG
            exact hcomp.2 (by
              simpa [Gsmall, SimpleGraph.comap_adj, embB] using hG)
        · simpa [embB] using (Finset.card_map embB (s := I)).trans hI.card_eq
      have hv_adj_compl : ∀ w ∈ I.map embB, Gᶜ.Adj v w := by
        intro w hw
        rcases Finset.mem_map.mp hw with ⟨x, hx, rfl⟩
        have hxB : embB x ∈ B := (eB.symm x).property
        have hxnon : embB x ∈ nonneigh := hBsub hxB
        have hxrest : embB x ∈ rest := (Finset.mem_filter.mp hxnon).1
        have hxnot : ¬ G.Adj v (embB x) := (Finset.mem_filter.mp hxnon).2
        have hxne : v ≠ embB x := by
          have hne' : embB x ≠ v := (Finset.mem_erase.mp hxrest).1
          exact fun h => hne' h.symm
        exact ⟨hxne, hxnot⟩
      right
      exact ⟨insert v (I.map embB), hMapped.insert hv_adj_compl⟩
