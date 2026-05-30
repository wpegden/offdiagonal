import Tablet.Digraph
import Mathlib.Data.Sym.Sym2.Order

-- [TABLET NODE: RandomHomomorphismColoring]

noncomputable def RandomHomomorphismColoring {W : Type} (D : Digraph W)
    (ell n : ℕ) (hell : 1 ≤ ell) (phi : Fin (ell - 1) → Fin n → W) :
    Sym2 (Fin n) → Fin ell := by
-- BODY
  classical
  exact fun e =>
    let x : Fin n := (Sym2.sortEquiv e).1.1
    let y : Fin n := (Sym2.sortEquiv e).1.2
    if h : ∃ m : ℕ, ∃ hm : m < ell - 1, D (phi ⟨m, hm⟩ x) (phi ⟨m, hm⟩ y) then
      let m : ℕ := Nat.find h
      ⟨m, by
        have hm : m < ell - 1 := Classical.choose (Nat.find_spec h)
        omega⟩
    else
      ⟨ell - 1, by omega⟩
