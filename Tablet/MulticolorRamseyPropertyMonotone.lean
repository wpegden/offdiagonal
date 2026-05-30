import Tablet.MulticolorRamseyProperty

-- [TABLET NODE: MulticolorRamseyPropertyMonotone]

theorem MulticolorRamseyPropertyMonotone (s ell m n : ℕ)
    (hmn : m ≤ n) (hm : MulticolorRamseyProperty s ell m) :
    MulticolorRamseyProperty s ell n := by
-- BODY
  classical
  intro color
  let emb : Fin m ↪ Fin n := Fin.castLEEmb hmn
  let colorSmall : Sym2 (Fin m) → Fin ell := fun e => color (Sym2.map emb e)
  rcases hm colorSmall with ⟨S, hS_card, c, hS_mono⟩
  refine ⟨S.map emb, ?_⟩
  refine ⟨?_, c, ?_⟩
  · simpa [emb] using (Finset.card_map emb (s := S)).trans hS_card
  · intro u v hu hv huv
    rcases Finset.mem_map.mp hu with ⟨u', hu', rfl⟩
    rcases Finset.mem_map.mp hv with ⟨v', hv', rfl⟩
    have huv' : u' ≠ v' := by
      intro hEq
      exact huv (by simpa [emb] using congrArg emb hEq)
    simpa [colorSmall, emb, Sym2.map_mk] using hS_mono u' v' hu' hv' huv'

