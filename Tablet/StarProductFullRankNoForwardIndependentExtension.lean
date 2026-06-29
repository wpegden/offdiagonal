import Tablet.StarProductExtensionOrthogonalToPrefixSpan
import Tablet.StarProductPrefixRank

-- [TABLET NODE: StarProductFullRankNoForwardIndependentExtension]

universe u

theorem StarProductFullRankNoForwardIndependentExtension (K : Type u) [Field K] (t : ℕ)
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (b : Projectivization K (Fin (t + 1) → K))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (hxb : x.val.2 = b)
    (hrank : StarProductPrefixRank K t p b = t + 1) :
    ¬ ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) := by
-- BODY
  intro hfi
  have horth := StarProductExtensionOrthogonalToPrefixSpan K t p x hfi
  have htop : StarProductPrefixSpan K t p b = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    simpa [StarProductPrefixRank] using hrank
  have hall : ∀ v : Fin (t + 1) → K, Projectivization.rep x.val.1 ⬝ᵥ v = 0 := by
    intro v
    have hv : v ∈ StarProductPrefixSpan K t p x.val.2 := by
      rw [hxb, htop]
      exact Submodule.mem_top
    exact horth v hv
  exact Projectivization.rep_nonzero x.val.1 ((dotProduct_eq_zero_iff).mp hall)
