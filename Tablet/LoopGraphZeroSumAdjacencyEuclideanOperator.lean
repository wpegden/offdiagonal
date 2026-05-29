import Tablet.LoopGraphAdjacencyEuclideanOperatorMapsZeroSum

-- [TABLET NODE: LoopGraphZeroSumAdjacencyEuclideanOperator]

universe u

noncomputable def LoopGraphZeroSumAdjacencyEuclideanOperator {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) :
    LoopGraphEuclideanZeroSumSubmodule V →ₗ[ℝ]
      LoopGraphEuclideanZeroSumSubmodule V :=
-- BODY
  { toFun := fun x =>
      ⟨LoopGraphAdjacencyEuclideanOperator G x,
        LoopGraphAdjacencyEuclideanOperatorMapsZeroSum G n d lambda hG x x.property⟩
    map_add' := by
      intro x y
      ext v
      simp
    map_smul' := by
      intro c x
      ext v
      simp }
