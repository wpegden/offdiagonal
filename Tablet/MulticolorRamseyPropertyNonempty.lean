import Tablet.MulticolorRamseyProperty
import Tablet.RamseyPropertyNonempty

-- [TABLET NODE: MulticolorRamseyPropertyNonempty]

theorem MulticolorRamseyPropertyNonempty (s ell : ℕ) (hell : 0 < ell) :
    ({n : ℕ | MulticolorRamseyProperty s ell n} : Set ℕ).Nonempty := by
-- BODY
  induction ell with
  | zero => cases hell
  | succ ell ih =>
      by_cases hell_zero : ell = 0
      · subst ell
        refine ⟨s, ?_⟩
        intro color
        refine ⟨Finset.univ, ?_, ⟨0, by omega⟩, ?_⟩
        · simp
        · intro u v hu hv huv
          apply Fin.ext
          omega
      · have hell_pos : 0 < ell := Nat.pos_of_ne_zero hell_zero
        rcases ih hell_pos with ⟨m, hm⟩
        rcases RamseyPropertyNonempty s m with ⟨N, hN⟩
        refine ⟨N, ?_⟩
        intro color
        let last : Fin (ell + 1) := ⟨ell, Nat.lt_succ_self ell⟩
        let G : SimpleGraph (Fin N) :=
          SimpleGraph.fromRel (fun u v : Fin N => color (Sym2.mk u v) = last)
        rcases hN G with hLast | hOther
        · rcases hLast with ⟨S, hS⟩
          refine ⟨S, hS.card_eq, last, ?_⟩
          intro u v hu hv huv
          have hG : G.Adj u v := hS.isClique hu hv huv
          rcases (SimpleGraph.fromRel_adj
            (fun u v : Fin N => color (Sym2.mk u v) = last) u v).mp hG with
            ⟨_hne, hrel | hrel⟩
          · exact hrel
          · simpa [Sym2.eq_swap] using hrel
        · rcases hOther with ⟨I, hI⟩
          let emb : Fin m ↪ Fin N := (I.orderEmbOfFin hI.card_eq).toEmbedding
          let colorSmall : Sym2 (Fin m) → Fin ell := fun e =>
            if hlast : color (Sym2.map emb e) = last then
              ⟨0, hell_pos⟩
            else
              ⟨(color (Sym2.map emb e)).val, by
                have hlt := (color (Sym2.map emb e)).isLt
                have hne_last_val : (color (Sym2.map emb e)).val ≠ ell := by
                  intro hval
                  apply hlast
                  ext
                  exact hval
                omega⟩
          rcases hm colorSmall with ⟨S, hS_card, c, hS_mono⟩
          refine ⟨S.map emb, ?_⟩
          refine ⟨?_, (⟨c.val, by omega⟩ : Fin (ell + 1)), ?_⟩
          · simpa [emb] using (Finset.card_map emb (s := S)).trans hS_card
          · intro u v hu hv huv
            rcases Finset.mem_map.mp hu with ⟨u', hu', rfl⟩
            rcases Finset.mem_map.mp hv with ⟨v', hv', rfl⟩
            have huv' : u' ≠ v' := by
              intro hEq
              exact huv (by simpa [emb] using congrArg emb hEq)
            have hcomp : Gᶜ.Adj (emb u') (emb v') :=
              hI.isClique
                (by
                  dsimp [emb]
                  exact Finset.orderEmbOfFin_mem I hI.card_eq u')
                (by
                  dsimp [emb]
                  exact Finset.orderEmbOfFin_mem I hI.card_eq v')
                (by
                  intro hEq
                  exact huv' (by simpa [emb] using (I.orderEmbOfFin hI.card_eq).injective hEq))
            have hnotlast : color (Sym2.mk (emb u') (emb v')) ≠ last := by
              intro hlast
              have hG : G.Adj (emb u') (emb v') := by
                rw [SimpleGraph.fromRel_adj]
                exact ⟨by
                  intro hEq
                  exact huv' (by simpa [emb] using (I.orderEmbOfFin hI.card_eq).injective hEq),
                  Or.inl hlast⟩
              exact hcomp.2 hG
            have hsmall := hS_mono u' v' hu' hv' huv'
            have hsmall' :
                (⟨(color (Sym2.mk (emb u') (emb v'))).val, by
                    have hlt := (color (Sym2.mk (emb u') (emb v'))).isLt
                    have hne_last_val :
                        (color (Sym2.mk (emb u') (emb v'))).val ≠ ell := by
                      intro hval
                      apply hnotlast
                      ext
                      exact hval
                    omega⟩ : Fin ell) = c := by
              have hnotlast' :
                  color (Sym2.mk ((I.orderEmbOfFin hI.card_eq) u')
                    ((I.orderEmbOfFin hI.card_eq) v')) ≠ last := by
                simpa [emb] using hnotlast
              simpa [colorSmall, emb, Sym2.map_mk, hnotlast'] using hsmall
            have hval : (color (Sym2.mk (emb u') (emb v'))).val = c.val :=
              congrArg Fin.val hsmall'
            exact Fin.ext hval

