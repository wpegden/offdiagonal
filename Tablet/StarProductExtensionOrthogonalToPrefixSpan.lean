import Tablet.StarProductForwardIndependentConsistentTuple
import Tablet.StarProductPrefixSpan

-- [TABLET NODE: StarProductExtensionOrthogonalToPrefixSpan]

universe u

theorem StarProductExtensionOrthogonalToPrefixSpan (K : Type u) [Field K] (t : ℕ)
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (hfi : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x)) :
    ∀ v ∈ StarProductPrefixSpan K t p x.val.2,
      Projectivization.rep x.val.1 ⬝ᵥ v = 0 := by
-- BODY
  classical
  let L : (Fin (t + 1) → K) →ₗ[K] K :=
    { toFun := fun v => Projectivization.rep x.val.1 ⬝ᵥ v
      map_add' := by
        intro v w
        exact dotProduct_add _ _ _
      map_smul' := by
        intro c v
        exact dotProduct_smul c _ _ }
  have hcons :
      StarProductConsistentTuple (PolarityGraph K t)
        (fun i : Fin (m + 1) =>
          ((@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) i).val.1)
        (fun i : Fin (m + 1) =>
          ((@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) i).val.2) := by
    exact (StarProductForwardIndependentConsistentTuple
      (PolarityGraph K t)
      (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x)).mp hfi
  have hspan_le :
      StarProductPrefixSpan K t p x.val.2 ≤ LinearMap.ker L := by
    rw [StarProductPrefixSpan]
    refine Submodule.span_le.mpr ?_
    rintro v ⟨i, hi_edge, rfl⟩
    change L (Projectivization.rep (p i).val.2) = 0
    have hcross :
        PolarityGraph K t x.val.1 (p i).val.2 := by
      have h := hcons.2 i.castSucc (Fin.last m) (Fin.castSucc_lt_last i)
      have hi' :
          PolarityGraph K t
            (((@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x)
              i.castSucc).val.1)
            (((@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x)
              (Fin.last m)).val.2) := by
        simpa using hi_edge
      have hres := h hi'
      simpa using hres
    change Projectivization.rep x.val.1 ⬝ᵥ Projectivization.rep (p i).val.2 = 0
    have hmk :
        Projectivization.orthogonal
          (Projectivization.mk K (Projectivization.rep x.val.1)
            (Projectivization.rep_nonzero x.val.1))
          (Projectivization.mk K (Projectivization.rep (p i).val.2)
            (Projectivization.rep_nonzero (p i).val.2)) := by
      simpa [Projectivization.mk_rep, PolarityGraph] using hcross
    exact (Projectivization.orthogonal_mk
      (Projectivization.rep_nonzero x.val.1)
      (Projectivization.rep_nonzero (p i).val.2)).mp hmk
  intro v hv
  exact hspan_le hv
