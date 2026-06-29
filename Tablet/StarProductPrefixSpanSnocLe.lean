import Tablet.StarProductPrefixSpan

-- [TABLET NODE: StarProductPrefixSpanSnocLe]

universe u

theorem StarProductPrefixSpanSnocLe (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (y : Projectivization K (Fin (t + 1) → K)) :
    StarProductPrefixSpan K t p y ≤
      StarProductPrefixSpan K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) y := by
-- BODY
  classical
  rw [StarProductPrefixSpan, StarProductPrefixSpan]
  refine Submodule.span_mono ?_
  rintro v ⟨i, hiy, rfl⟩
  exact ⟨i.castSucc, by simpa using hiy, by simp⟩
