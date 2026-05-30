import Tablet.ForwardIndependentTuple
import Tablet.RandomHomomorphismColoring

-- [TABLET NODE: RandomHomomorphismFinalColorForwardIndependent]

theorem RandomHomomorphismFinalColorForwardIndependent {W : Type}
    (D : Digraph W) (s ell n : ℕ) (hell : 1 ≤ ell)
    (phi : Fin (ell - 1) → Fin n → W) :
    ∀ (v : Fin s → Fin n), StrictMono v →
      (∀ i j : Fin s, i < j →
        RandomHomomorphismColoring D ell n hell phi (Sym2.mk (v i) (v j)) =
          (⟨ell - 1, by omega⟩ : Fin ell)) →
      ∀ c : Fin (ell - 1), ForwardIndependentTuple D (fun i => phi c (v i)) := by
-- BODY
  classical
  intro v hv hfinal c i j hij harc
  have hxy : v i ≤ v j := le_of_lt (hv hij)
  have hcolor := hfinal i j hij
  dsimp [RandomHomomorphismColoring] at hcolor
  have hex : ∃ m : ℕ, ∃ hm : m < ell - 1,
      D (phi ⟨m, hm⟩ (min (v i) (v j))) (phi ⟨m, hm⟩ (max (v i) (v j))) := by
    refine ⟨c.val, c.isLt, ?_⟩
    simpa [min_eq_left hxy, max_eq_right hxy] using harc
  simp [hex] at hcolor
  have hfind_lt : Nat.find hex < ell - 1 := Classical.choose (Nat.find_spec hex)
  have hval : Nat.find hex = ell - 1 := hcolor
  omega
