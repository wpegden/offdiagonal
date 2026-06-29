import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic
import Tablet.StarProductExtensionOrthogonalToPrefixSpan
import Tablet.StarProductFixedBExtensionBound
import Tablet.StarProductPrefixRank

-- [TABLET NODE: StarProductFixedBRankLeExtensionBound]

universe u

open LinearMap Matrix

theorem StarProductFixedBRankLeExtensionBound (K : Type u) [Field K] [Fintype K]
    (t q r : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (b : Projectivization K (Fin (t + 1) → K))
    (hq : q = Fintype.card K)
    (hrank : StarProductPrefixRank K t p b = r)
    (hrle : r ≤ t)
    (hgeom : (∑ i ∈ Finset.range (t + 1 - r), q ^ i) ≤ 2 * q ^ (t - r))
    (Ext : Finset (Projectivization K (Fin (t + 1) → K)))
    (hExt : ∀ a ∈ Ext, ∃ x : ProductDigraphVertex (PolarityGraph K t),
      x.val.1 = a ∧ x.val.2 = b ∧
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
          (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x)) :
    Ext.card ≤ 2 * q ^ (t - r) := by
-- BODY
  classical
  have _hrle : r ≤ t := hrle
  let W := StarProductPrefixSpan K t p b
  let B : LinearMap.BilinForm K (Fin (t + 1) → K) :=
    Matrix.toBilin' (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) K)
  let Wperp : Submodule K (Fin (t + 1) → K) := B.orthogonal W
  have hB_apply : ∀ v w : Fin (t + 1) → K, B v w = v ⬝ᵥ w := by
    intro v w
    simp [B, Matrix.toBilin'_apply']
  have hB_nondeg : B.Nondegenerate := by
    dsimp [B]
    exact LinearMap.BilinForm.nondegenerate_toBilin'_of_det_ne_zero'
      (1 : Matrix (Fin (t + 1)) (Fin (t + 1)) K) (by simp)
  have hdim : Module.finrank K Wperp = t + 1 - r := by
    have h := LinearMap.BilinForm.finrank_orthogonal (B := B) hB_nondeg W
    have hWrank : Module.finrank K W = r := by
      simpa [W, StarProductPrefixRank] using hrank
    calc
      Module.finrank K Wperp = Module.finrank K (Fin (t + 1) → K) - Module.finrank K W := h
      _ = (t + 1) - r := by
        simp [hWrank, Module.finrank_fintype_fun_eq_card]
  have hLift : ∀ a ∈ Ext, ∃ x : Projectivization K Wperp,
      Projectivization.map Wperp.subtype Wperp.injective_subtype x = a := by
    letI : Fintype Wperp := Fintype.ofFinite _
    letI : Fintype (Projectivization K Wperp) := Fintype.ofFinite _
    intro a ha
    obtain ⟨x, hxa, hxb, hfi⟩ := hExt a ha
    have horth := StarProductExtensionOrthogonalToPrefixSpan K t p x hfi
    have ha_mem : Projectivization.rep a ∈ Wperp := by
      rw [← hxa]
      intro w hw
      change B w (Projectivization.rep x.val.1) = 0
      rw [hB_apply]
      rw [dotProduct_comm]
      exact horth w (by simpa [W, hxb] using hw)
    let y : Wperp := ⟨Projectivization.rep a, ha_mem⟩
    have hyne : y ≠ 0 := by
      intro hy
      exact Projectivization.rep_nonzero a (Subtype.ext_iff.mp hy)
    refine ⟨Projectivization.mk K y hyne, ?_⟩
    rw [Projectivization.map_mk]
    change Projectivization.mk K (Projectivization.rep a) _ = a
    exact Projectivization.mk_rep a
  letI : Fintype Wperp := Fintype.ofFinite _
  letI : Fintype (Projectivization K Wperp) := Fintype.ofFinite _
  exact StarProductFixedBExtensionBound K t q r Wperp hq hdim hgeom Ext hLift
