import Tablet.HsFreePair
import Tablet.ForwardIndependentTupleCount
import Tablet.ProductDigraph
import Tablet.ProductDigraphShrinkingSequenceBound
import Tablet.ProductDigraphTransitiveFree
import Tablet.ProductDigraphVertex
import Tablet.ProductDigraphVertexCard
import Tablet.ProductDigraphTupleHasShrinkingSequence
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: ProductDigraphForwardIndependentBound]

universe u

theorem ProductDigraphForwardIndependentBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (s n dF dG : ℕ) (lambdaF lambdaG eta w : ℝ)
    (hs : 3 ≤ s) (hn : 3 ≤ n) (hdF : 0 < dF) (hdG : 0 < dG)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hFG : HsFreePair F G s)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (hw : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ))
    (heta_nonneg : 0 ≤ eta) (heta_le_one : eta ≤ 1) :
    ∃ (W : Type u) (_ : Fintype W), ∃ D : Digraph W,
      TransitiveTournamentFree D s ∧
        Fintype.card W = dF * n ∧
          ∀ k : ℕ, w ≤ (k : ℝ) →
            ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤
              (16 : ℝ) ^ k * Real.rpow eta ((k : ℝ) - w) *
                ((dF * n : ℕ) : ℝ) ^ k := by
-- BODY
  classical
  letI : Fintype (ProductDigraphVertex F) := Fintype.ofFinite _
  refine ⟨ProductDigraphVertex F, inferInstance, ProductDigraph F G, ?_, ?_, ?_⟩
  · exact ProductDigraphTransitiveFree F G s hFG
  · exact ProductDigraphVertexCard F n dF lambdaF hF
  · intro k hk
    let shrinkingSequence :
        {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v} → Fin k → Bool :=
      fun v i =>
        decide
          (((dG : ℝ) *
                ((((Finset.univ.filter
                  (fun b : V => ∀ j : Fin k, j < i → ¬ G (v.val j).val.1 b)).card :
                    ℕ) : ℝ))) /
              (2 * (n : ℝ)) <
            ((LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V)
              (Finset.univ.filter
                (fun b : V => ∀ j : Fin k, j < i → ¬ G (v.val j).val.1 b)) :
                ℕ) : ℝ))
    have hshrinkingSequence :
        ∀ v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v},
          ProductDigraphTupleHasShrinkingSequence F G n dG v.val (shrinkingSequence v) := by
      intro v
      unfold ProductDigraphTupleHasShrinkingSequence
      refine ⟨v.property, ?_⟩
      intro i
      simp [shrinkingSequence]
    sorry
