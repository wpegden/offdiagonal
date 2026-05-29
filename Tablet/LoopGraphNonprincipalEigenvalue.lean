import Tablet.LoopGraphAdjacencyAction

-- [TABLET NODE: LoopGraphNonprincipalEigenvalue]

universe u

noncomputable def LoopGraphNonprincipalEigenvalue {V : Type u} [Fintype V]
    (G : LoopGraph V) (mu : ℝ) : Prop :=
-- BODY
  ∃ f : V → ℝ,
    (∃ v : V, f v ≠ 0) ∧
      Finset.univ.sum (fun v => f v) = 0 ∧
        ∀ v : V, LoopGraphAdjacencyAction G f v = mu * f v
