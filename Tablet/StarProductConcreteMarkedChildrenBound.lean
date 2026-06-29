import Mathlib.Tactic
import Tablet.StarProductConcreteMarkedChildrenCertificate
import Tablet.StarProductPopularChildrenBound
import Tablet.StarProductPoorChildrenBound

-- [TABLET NODE: StarProductConcreteMarkedChildrenBound]

universe u

theorem StarProductConcreteMarkedChildrenBound (K : Type u)
    [Field K] [Fintype K] (t q A h k : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    (hA : 10128 * t ≤ A) (hh : A * q ^ t ≤ h) :
    ∀ (m : ℕ), m < k → ∀ p : Fin m → ProductDigraphVertex (PolarityGraph K t),
      ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) p →
        Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
          ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
              (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ∧
            StarProductConcreteMarked K t q
              (fun _ p r => StarProductLayerChoice K t p r) m p x = true} ≤ h := by
-- BODY
  exact
    StarProductConcreteMarkedChildrenCertificate K t q A h k
      (fun _ p r => StarProductLayerChoice K t p r)
      (StarProductPopularChildrenBound K t q k ht hq)
      (StarProductPoorChildrenBound K t q k ht hq)
      hA hh
