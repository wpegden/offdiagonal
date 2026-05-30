import Tablet.RandomHomomorphismFinalColorForwardIndependent
import Mathlib.Data.Finset.Sort

-- [TABLET NODE: RandomHomomorphismFinalColorCliqueToForwardIndependent]

theorem RandomHomomorphismFinalColorCliqueToForwardIndependent {W : Type}
    (D : Digraph W) (s ell n : ℕ) (hell : 1 ≤ ell)
    (phi : Fin (ell - 1) → Fin n → W) :
    ∀ S : Finset (Fin n), S.card = s →
      (∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v →
        RandomHomomorphismColoring D ell n hell phi (Sym2.mk u v) =
          (⟨ell - 1, by omega⟩ : Fin ell)) →
      ∃ v : Fin s → Fin n, StrictMono v ∧ (∀ i, v i ∈ S) ∧
        ∀ c : Fin (ell - 1), ForwardIndependentTuple D (fun i => phi c (v i)) := by
-- BODY
  classical
  intro S hcard hfinal
  let vEmb := S.orderEmbOfFin hcard
  let v : Fin s → Fin n := fun i => vEmb i
  have hv : StrictMono v := vEmb.strictMono
  have hmem : ∀ i, v i ∈ S := by
    intro i
    exact Finset.orderEmbOfFin_mem S hcard i
  have hfinal_ordered :
      ∀ i j : Fin s, i < j →
        RandomHomomorphismColoring D ell n hell phi (Sym2.mk (v i) (v j)) =
          (⟨ell - 1, by omega⟩ : Fin ell) := by
    intro i j hij
    exact hfinal (v i) (v j) (hmem i) (hmem j) (ne_of_lt (hv hij))
  exact ⟨v, hv, hmem,
    RandomHomomorphismFinalColorForwardIndependent D s ell n hell phi v hv hfinal_ordered⟩
