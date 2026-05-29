import Tablet.LoopGraphDegree
import Tablet.LoopGraphNonprincipalEigenvalue
import Tablet.LoopGraphSymmetric

-- [TABLET NODE: LoopGraphNdLambda]

universe u

noncomputable def LoopGraphNdLambda {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ) : Prop :=
-- BODY
  Fintype.card V = n ∧
    LoopGraphSymmetric G ∧
      (∀ v : V, LoopGraphDegree G v = d) ∧
        (∀ mu : ℝ, LoopGraphNonprincipalEigenvalue G mu → |mu| ≤ lambda) ∧
          0 ≤ lambda
