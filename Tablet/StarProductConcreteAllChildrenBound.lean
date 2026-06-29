import Tablet.StarProductForwardIndependentChildCountLeVertices
import Tablet.StarProductPolarityVertexCountBound

-- [TABLET NODE: StarProductConcreteAllChildrenBound]

universe u

theorem StarProductConcreteAllChildrenBound (K : Type u) [Field K] [Fintype K]
    (t q Delta k : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    (hn : ((q ^ (t + 1) - 1) / (q - 1)) ≤ 2 * q ^ t)
    (hd : ((q ^ t - 1) / (q - 1)) ≤ 2 * q ^ (t - 1))
    (hDelta : 4 * q ^ (2 * t - 1) ≤ Delta) :
    ∀ (m : ℕ), m < k → ∀ p : Fin m → ProductDigraphVertex (PolarityGraph K t),
      ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) p →
        Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
          ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
            (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x)} ≤ Delta := by
-- BODY
  intro m _ p _hp
  exact (StarProductForwardIndependentChildCountLeVertices
    (PolarityGraph K t) p).trans
      ((StarProductPolarityVertexCountBound K t q ht hq hn hd).trans hDelta)
