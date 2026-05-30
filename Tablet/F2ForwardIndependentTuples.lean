import Tablet.DigraphLoopless
import Tablet.F2CoordinateDigraphLoopless
import Tablet.F2CoordinateDigraphTransitiveFree
import Tablet.ForwardIndependentTupleCount
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: F2ForwardIndependentTuples]

universe u

theorem F2ForwardIndependentTuples :
    ∀ s k : ℕ, 4 ≤ s → s ≤ k →
      ∃ (W : Type) (_ : Fintype W), ∃ D : Digraph W,
        DigraphLoopless D ∧
          TransitiveTournamentFree D s ∧
            Fintype.card W = 2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1 ∧
              ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤
                Finset.sum (Finset.Icc 1 (s - 1))
                  (fun t => ((Nat.choose k t : ℕ) : ℝ) *
                    Real.rpow 2
                      ((((s - 1) * (t + k) - Nat.choose (t + 1) 2 : ℕ) : ℝ))) := by
-- BODY
  classical
  intro s k hs hsk
  let N : ℕ := 2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1
  let p : ℕ := s - 1
  let Vec : Type := Fin p → ZMod 2
  let U : Type := {z : Vec × Vec // z.1 ⬝ᵥ z.2 = 1}
  have hEmbedding : Nonempty (Fin N ↪ U) := by
    sorry
  rcases hEmbedding with ⟨e⟩
  let x : Fin N → Vec := fun w => (e w).val.1
  let y : Fin N → Vec := fun w => (e w).val.2
  let D : Digraph (Fin N) := fun a b => x a ⬝ᵥ y b = 0
  have hdiag : ∀ w : Fin N, x w ⬝ᵥ y w = 1 := by
    intro w
    exact (e w).property
  refine ⟨Fin N, inferInstance, D, ?_, ?_, ?_, ?_⟩
  · exact F2CoordinateDigraphLoopless x y hdiag
  · have hps : p < s := by
      dsimp [p]
      omega
    exact F2CoordinateDigraphTransitiveFree hps x y hdiag
  · simp [N]
  · sorry
