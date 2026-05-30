import Tablet.DigraphLoopless

-- [TABLET NODE: F2CoordinateDigraphLoopless]

universe u

theorem F2CoordinateDigraphLoopless {p : ℕ} {W : Type u}
    (x y : W → Fin p → ZMod 2)
    (hdiag : ∀ w : W, x w ⬝ᵥ y w = 1) :
    DigraphLoopless (fun a b : W => x a ⬝ᵥ y b = 0) := by
-- BODY
  intro w hloop
  have hone : (1 : ZMod 2) = 0 := by
    rw [← hdiag w]
    exact hloop
  exact one_ne_zero hone
