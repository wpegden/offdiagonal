import Tablet.ProductDigraphVertex
import Tablet.LoopGraphNdLambda

-- [TABLET NODE: ProductDigraphVertexCard]

universe u

theorem ProductDigraphVertexCard {V : Type u} [Fintype V]
    (F : LoopGraph V) (n dF : ℕ) (lambdaF : ℝ)
    [Fintype (ProductDigraphVertex F)]
    (hF : LoopGraphNdLambda F n dF lambdaF) :
    Fintype.card (ProductDigraphVertex F) = dF * n := by
-- BODY
  classical
  let e : ProductDigraphVertex F ≃ (Sigma fun a : V => {b : V // F a b}) :=
    { toFun := fun p => ⟨p.val.1, ⟨p.val.2, p.property⟩⟩
      invFun := fun q => ⟨(q.1, q.2.val), q.2.property⟩
      left_inv := by
        intro p
        cases p with
        | mk p hp =>
          cases p
          rfl
      right_inv := by
        intro q
        cases q with
        | mk a b =>
          cases b
          rfl }
  have hfiber :
      ∀ a : V, Fintype.card {b : V // F a b} = LoopGraphDegree F a := by
    intro a
    rw [Fintype.card_subtype]
    simp [LoopGraphDegree]
  calc
    Fintype.card (ProductDigraphVertex F)
        = Fintype.card (Sigma fun a : V => {b : V // F a b}) :=
          Fintype.card_congr e
    _ = ∑ a : V, Fintype.card {b : V // F a b} := by
          simp
    _ = ∑ a : V, dF := by
          apply Finset.sum_congr rfl
          intro a ha
          rw [hfiber a, hF.2.2.1 a]
    _ = Fintype.card V * dF := by
          simp
    _ = n * dF := by
          rw [hF.1]
    _ = dF * n := by
          rw [Nat.mul_comm]
