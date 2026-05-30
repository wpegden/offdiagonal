import Tablet.DigraphLoopless
import Tablet.F2CoordinateDigraphLoopless
import Tablet.F2CoordinateDigraphTransitiveFree
import Tablet.F2BadTupleAmbientStepProductBound
import Tablet.F2BadTupleFixedIncreasePrefixRestriction
import Tablet.F2BadTupleFixedIncreaseTrueLastBound
import Tablet.F2BadTupleFixedIncreaseCount
import Tablet.F2BadTupleLastPairAmbientFiberBound
import Tablet.F2BadTupleLastPairSpanFiberBound
import Tablet.F2BadTuple
import Tablet.F2BadTupleNonincreaseStepProductBound
import Tablet.F2BadTuplePrefixFiberBound
import Tablet.F2BadTuplePrefixSpanCard
import Tablet.F2BadTupleRankAmbientBound
import Tablet.F2BadTupleRankIncreaseSetCard
import Tablet.F2BadTupleRankOne
import Tablet.F2BadTupleRankStep
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
    have hk_pos : 0 < k := by omega
    have hbad_rank_one :
        ∀ ab : Bad, F2BadTupleRank p k ab.val 1 = 1 := by
      intro ab
      exact F2BadTupleRankOne p k ab.val ab.property hk_pos
    have hbad_rank_le_p :
        ∀ (ab : Bad) (i : ℕ), F2BadTupleRank p k ab.val i ≤ p := by
      intro ab i
      exact F2BadTupleRankAmbientBound p k ab.val i
    have hbad_rank_step :
        ∀ (ab : Bad) (i : ℕ), i < k →
          F2BadTupleRank p k ab.val (i + 1) = F2BadTupleRank p k ab.val i ∨
            F2BadTupleRank p k ab.val (i + 1) = F2BadTupleRank p k ab.val i + 1 := by
      intro ab i hi
      exact F2BadTupleRankStep p k ab.val hi
    have hbad_prefix_fiber_bound :
        ∀ (ab : Bad) (i : ℕ),
          Fintype.card
              {y : Vec //
                ∀ j : {j : Fin k // j.val < i}, (ab.val j.1).1 ⬝ᵥ y = 1} ≤
            2 ^ (p - F2BadTupleRank p k ab.val i) := by
      intro ab i
      exact F2BadTuplePrefixFiberBound p k ab.val i
    have hbad_rank_increase_data :
        ∀ ab : Bad,
          F2BadTupleRank p k ab.val k ∈ Finset.Icc 1 p ∧
            (F2BadTupleRankIncreaseSet p k ab.val).card =
              F2BadTupleRank p k ab.val k := by
      intro ab
      exact F2BadTupleRankIncreaseSetCard p k ab.val ab.property hk_pos
    have hbad_prefix_span_card :
        ∀ (ab : Bad) (i : ℕ),
          Nat.card
              (Submodule.span (ZMod 2)
                (Set.range (fun j : {j : Fin k // j.val < i} => (ab.val j.1).1))) =
            2 ^ F2BadTupleRank p k ab.val i := by
      intro ab i
      exact F2BadTuplePrefixSpanCard p k ab.val i
    have hbad_ambient_step_product_bound :
        ∀ (ab : Bad) (i : ℕ),
          Fintype.card Vec *
              Fintype.card
                {y : Vec //
                  ∀ j : {j : Fin k // j.val < i}, (ab.val j.1).1 ⬝ᵥ y = 1} ≤
            2 ^ p * 2 ^ (p - F2BadTupleRank p k ab.val i) := by
      intro ab i
      exact F2BadTupleAmbientStepProductBound p k ab.val i
    have hbad_nonincrease_step_product_bound :
        ∀ (ab : Bad) (i : ℕ) (hi : i < k),
          F2BadTupleRank p k ab.val (i + 1) = F2BadTupleRank p k ab.val i →
            (ab.val ⟨i, hi⟩).1 ∈
                Submodule.span (ZMod 2)
                  (Set.range (fun j : {j : Fin k // j.val < i} => (ab.val j.1).1)) ∧
              Nat.card
                  (Submodule.span (ZMod 2)
                    (Set.range (fun j : {j : Fin k // j.val < i} => (ab.val j.1).1))) *
                  Fintype.card
                    {y : Vec //
                      ∀ j : {j : Fin k // j.val < i + 1},
                        (ab.val j.1).1 ⬝ᵥ y = 1} ≤
                2 ^ F2BadTupleRank p k ab.val i *
                  2 ^ (p - F2BadTupleRank p k ab.val i) := by
      intro ab i hi hsame
      exact F2BadTupleNonincreaseStepProductBound p k ab.val hi hsame
    have hbad_fixed_increase_count_available :
        ∀ z : Fin k → Bool,
          F2BadTupleFixedIncreaseCount p k z =
            Fintype.card
              {ab : Fin k → Vec × Vec //
                F2BadTuple p k ab ∧
                  ∀ i : Fin k,
                    (F2BadTupleRank p k ab (i.val + 1) =
                        F2BadTupleRank p k ab i.val + 1) ↔ z i = true} := by
      intro z
      rfl
    have hbad_prefix_restriction_available :
        ∀ (ab : Fin (k + 1) → Vec × Vec),
          F2BadTuple p (k + 1) ab →
            F2BadTuple p k (fun i : Fin k => ab i.castSucc) := by
      intro ab hbad
      exact F2BadTuplePrefixRestriction p k ab hbad
    have hbad_rank_prefix_restriction_available :
        ∀ (ab : Fin (k + 1) → Vec × Vec) (i : ℕ), i ≤ k →
          F2BadTupleRank p (k + 1) ab i =
            F2BadTupleRank p k (fun j : Fin k => ab j.castSucc) i := by
      intro ab i hi
      exact F2BadTupleRankPrefixRestriction p k ab i hi
    have hbad_fixed_increase_prefix_restriction_available :
        ∀ (ab : Fin (k + 1) → Vec × Vec) (z : Fin (k + 1) → Bool),
          (F2BadTuple p (k + 1) ab ∧
              ∀ i : Fin (k + 1),
                (F2BadTupleRank p (k + 1) ab (i.val + 1) =
                    F2BadTupleRank p (k + 1) ab i.val + 1) ↔ z i = true) →
            F2BadTuple p k (fun i : Fin k => ab i.castSucc) ∧
              ∀ i : Fin k,
                (F2BadTupleRank p k (fun j : Fin k => ab j.castSucc) (i.val + 1) =
                    F2BadTupleRank p k (fun j : Fin k => ab j.castSucc) i.val + 1) ↔
                  z i.castSucc = true := by
      intro ab z hfixed
      exact F2BadTupleFixedIncreasePrefixRestriction p k ab z hfixed
    have hbad_last_b_choices_bound_available :
        ∀ (t : ℕ) (pref : Fin k → Vec × Vec) (a : Vec),
          Fintype.card
              {b : Vec //
                F2BadTupleRank p (k + 1)
                    (@Fin.snoc k (fun _ => Vec × Vec) pref (a, 0)) (k + 1) = t ∧
                  ∀ j : Fin (k + 1),
                    ((@Fin.snoc k (fun _ => Vec × Vec) pref (a, 0)) j).1 ⬝ᵥ b = 1} ≤
            2 ^ (p - t) := by
      intro t pref a
      exact F2BadTupleLastBChoicesBound p k t pref a
    have hbad_last_pair_ambient_fiber_bound_available :
        ∀ (t : ℕ) (pref : Fin k → Vec × Vec),
          Fintype.card
              {pair : Vec × Vec //
                F2BadTupleRank p (k + 1)
                    (@Fin.snoc k (fun _ => Vec × Vec) pref (pair.1, 0)) (k + 1) = t ∧
                  ∀ j : Fin (k + 1),
                    ((@Fin.snoc k (fun _ => Vec × Vec) pref (pair.1, 0)) j).1 ⬝ᵥ
                        pair.2 = 1} ≤
            2 ^ p * 2 ^ (p - t) := by
      intro t pref
      exact F2BadTupleLastPairAmbientFiberBound p k t pref
    sorry
