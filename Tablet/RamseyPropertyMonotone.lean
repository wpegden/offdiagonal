import Tablet.RamseyProperty

-- [TABLET NODE: RamseyPropertyMonotone]

theorem RamseyPropertyMonotone (s k m n : ℕ)
    (hmn : m ≤ n) (hm : RamseyProperty s k m) :
    RamseyProperty s k n := by
-- BODY
  classical
  intro G
  let emb : Fin m ↪ Fin n := Fin.castLEEmb hmn
  let Gsmall : SimpleGraph (Fin m) := SimpleGraph.comap (fun x => emb x) G
  rcases hm Gsmall with hClique | hIndependent
  · left
    rcases hClique with ⟨S, hS⟩
    refine ⟨S.map emb, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isClique_iff]
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro hEq
        exact hxy (by simpa [emb] using congrArg emb hEq)
      have hadj : Gsmall.Adj x' y' := hS.isClique hx' hy' hxy'
      simpa [Gsmall, SimpleGraph.comap_adj, emb] using hadj
    · simpa [emb] using (Finset.card_map emb (s := S)).trans hS.card_eq
  · right
    rcases hIndependent with ⟨I, hI⟩
    refine ⟨I.map emb, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isClique_iff]
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro hEq
        exact hxy (by simpa [emb] using congrArg emb hEq)
      have hcomp : Gsmallᶜ.Adj x' y' := hI.isClique hx' hy' hxy'
      refine ⟨?_, ?_⟩
      · exact hxy
      · intro hG
        exact hcomp.2 (by
          simpa [Gsmall, SimpleGraph.comap_adj, emb] using hG)
    · simpa [emb] using (Finset.card_map emb (s := I)).trans hI.card_eq
