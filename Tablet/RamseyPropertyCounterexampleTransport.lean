import Tablet.RamseyProperty

-- [TABLET NODE: RamseyPropertyCounterexampleTransport]

universe u

theorem RamseyPropertyCounterexampleTransport {W : Type u} [Fintype W]
    (H : SimpleGraph W) (s k : ℕ)
    (hNoClique : ¬ ∃ S : Finset W, H.IsNClique s S)
    (hNoIndependent : ¬ ∃ I : Finset W, Hᶜ.IsNClique k I) :
    ¬ RamseyProperty s k (Fintype.card W) := by
-- BODY
  classical
  intro hRamsey
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let Gfin : SimpleGraph (Fin (Fintype.card W)) := SimpleGraph.comap (fun x => e.symm x) H
  rcases hRamsey Gfin with hClique | hIndependent
  · apply hNoClique
    rcases hClique with ⟨S, hS⟩
    let emb : Fin (Fintype.card W) ↪ W := e.symm.toEmbedding
    refine ⟨S.map emb, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isClique_iff]
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro hEq
        exact hxy (by simpa [emb] using congrArg emb hEq)
      have hadj : Gfin.Adj x' y' := hS.isClique hx' hy' hxy'
      simpa [Gfin, SimpleGraph.comap_adj, emb] using hadj
    · simpa [emb] using (Finset.card_map emb (s := S)).trans hS.card_eq
  · apply hNoIndependent
    rcases hIndependent with ⟨I, hI⟩
    let emb : Fin (Fintype.card W) ↪ W := e.symm.toEmbedding
    refine ⟨I.map emb, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.isClique_iff]
      intro x hx y hy hxy
      rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
      rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro hEq
        exact hxy (by simpa [emb] using congrArg emb hEq)
      have hcomp : Gfinᶜ.Adj x' y' := hI.isClique hx' hy' hxy'
      refine ⟨?_, ?_⟩
      · exact hxy
      · intro hH
        exact hcomp.2 (by
          simpa [Gfin, SimpleGraph.comap_adj, emb] using hH)
    · simpa [emb] using (Finset.card_map emb (s := I)).trans hI.card_eq
