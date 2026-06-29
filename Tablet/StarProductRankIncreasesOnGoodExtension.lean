import Mathlib.Tactic
import Tablet.StarProductPrefixRank
import Tablet.StarProductPrefixSpanSnocLe

-- [TABLET NODE: StarProductRankIncreasesOnGoodExtension]

universe u

theorem StarProductRankIncreasesOnGoodExtension (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (y : Projectivization K (Fin (t + 1) → K)) (ell : ℕ)
    (hyrank : StarProductPrefixRank K t p y = ell)
    (hyedge : PolarityGraph K t x.val.1 y)
    (hnotspan : Projectivization.rep x.val.2 ∉ StarProductPrefixSpan K t p y) :
    ell + 1 ≤
      StarProductPrefixRank K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) y := by
-- BODY
  classical
  let W := StarProductPrefixSpan K t p y
  let W' := StarProductPrefixSpan K t
    (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) y
  have hWle : W ≤ W' := by
    simpa [W, W'] using StarProductPrefixSpanSnocLe K t p x y
  have hb_mem_W' : Projectivization.rep x.val.2 ∈ W' := by
    dsimp [W']
    rw [StarProductPrefixSpan]
    exact Submodule.subset_span
      ⟨Fin.last m, by simpa using hyedge, by simp⟩
  have hspan_le : K ∙ Projectivization.rep x.val.2 ≤ W' := by
    exact (Submodule.span_singleton_le_iff_mem
      (Projectivization.rep x.val.2) W').mpr hb_mem_W'
  let S : Submodule K (Fin (t + 1) → K) :=
    W ⊔ (K ∙ Projectivization.rep x.val.2)
  have hsup_le :
      S ≤ W' := by
    dsimp [S]
    exact sup_le hWle hspan_le
  have hsup_rank :
      Module.finrank K S = ell + 1 := by
    have h := Submodule.finrank_sup_span_singleton (K := K) (p := W)
      (v := Projectivization.rep x.val.2) (by simpa [W] using hnotspan)
    have hWrank : Module.finrank K W = ell := by
      simpa [W, StarProductPrefixRank] using hyrank
    calc
      Module.finrank K S =
          Module.finrank K W + 1 := by
            simpa [S] using h
      _ = ell + 1 := by rw [hWrank]
  have hmono := Submodule.finrank_mono hsup_le
  calc
    ell + 1 = Module.finrank K S := hsup_rank.symm
    _ ≤ Module.finrank K W' := hmono
    _ = StarProductPrefixRank K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) y := by
          rfl
