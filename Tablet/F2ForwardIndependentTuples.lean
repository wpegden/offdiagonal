import Tablet.DigraphLoopless
import Tablet.F2CoordinateDigraphLoopless
import Tablet.F2CoordinateDigraphTransitiveFree
import Tablet.F2BadTuple
import Tablet.F2BadTupleRankAmbientBound
import Tablet.F2BadTupleRankZero
import Tablet.F2DotOnePairEmbedding
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
    dsimp [N, p, Vec, U]
    simpa using F2DotOnePairEmbedding s hs
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
  · let Bad : Type :=
      {ab : Fin k → Vec × Vec //
        F2BadTuple p k ab}
    have hzmod_ne_zero_eq_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by
      intro a ha
      fin_cases a
      · exact (ha rfl).elim
      · rfl
    have hcount_le_bad :
        ForwardIndependentTupleCount D k ≤ Fintype.card Bad := by
      dsimp [ForwardIndependentTupleCount]
      refine Fintype.card_le_of_injective
        (fun v : {v : Fin k → Fin N // ForwardIndependentTuple D v} => by
          refine (⟨fun i => (x (v.val i), y (v.val i)), ?_⟩ : Bad)
          dsimp [F2BadTuple]
          intro i j hji
          by_cases hEq : j = i
          · subst j
            exact hdiag (v.val i)
          · have hlt : j < i := lt_of_le_of_ne hji hEq
            have hnot : ¬ x (v.val j) ⬝ᵥ y (v.val i) = 0 := by
              simpa [D] using v.property j i hlt
            exact hzmod_ne_zero_eq_one _ hnot) ?_
      · intro v₁ v₂ hv
        apply Subtype.ext
        funext i
        apply e.injective
        apply Subtype.ext
        exact congrFun (congrArg Subtype.val hv) i
    have hcount_le_bad_real :
        ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤ (Fintype.card Bad : ℝ) := by
      exact_mod_cast hcount_le_bad
    have hbad_initial_rank :
        ∀ ab : Bad, F2BadTupleRank p k ab.val 0 = 0 := by
      intro ab
      exact F2BadTupleRankZero p k ab.val
    have hbad_rank_le_p :
        ∀ (ab : Bad) (i : ℕ), F2BadTupleRank p k ab.val i ≤ p := by
      intro ab i
      exact F2BadTupleRankAmbientBound p k ab.val i
    sorry
