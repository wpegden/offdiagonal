import Tablet.ForwardIndependentTuple

-- [TABLET NODE: ForwardIndependentTupleCount]

universe u

noncomputable def ForwardIndependentTupleCount {V : Type u} [Fintype V]
    (D : Digraph V) (k : ℕ) : ℕ := by
-- BODY
  classical
  letI : DecidablePred (fun v : Fin k → V => ForwardIndependentTuple (k := k) D v) :=
    Classical.decPred _
  exact Fintype.card {v : Fin k → V // ForwardIndependentTuple (k := k) D v}
