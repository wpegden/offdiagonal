import Tablet.ForwardIndependentTuple
import Tablet.LoopGraphEdgeCountBetween
import Tablet.ProductDigraph

-- [TABLET NODE: ProductDigraphTupleHasShrinkingSequence]

universe u

noncomputable def ProductDigraphTupleHasShrinkingSequence {V : Type u} [Fintype V]
    (F G : LoopGraph V) (n dG : ℕ) {t : ℕ}
    (v : Fin t → ProductDigraphVertex F) (z : Fin t → Bool) : Prop := by
-- BODY
  classical
  exact
    ForwardIndependentTuple (ProductDigraph F G) v ∧
      ∀ i : Fin t,
        (z i = true ↔
          ((dG : ℝ) *
              ((((Finset.univ.filter
                (fun b : V => ∀ j : Fin t, j < i → ¬ G (v j).val.1 b)).card : ℕ) : ℝ))) /
              (2 * (n : ℝ)) <
            ((LoopGraphEdgeCountBetween G ({(v i).val.1} : Finset V)
              (Finset.univ.filter
                (fun b : V => ∀ j : Fin t, j < i → ¬ G (v j).val.1 b)) : ℕ) : ℝ))
