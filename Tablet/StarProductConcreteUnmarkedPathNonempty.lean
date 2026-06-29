import Mathlib.Tactic
import Tablet.StarProductConcreteMarked
import Tablet.StarProductConcreteUnmarkedExtensionNonempty
import Tablet.StarProductConcreteUnmarkedPsiApply
import Tablet.StarProductForwardIndependentExtensionRankLe
import Tablet.StarProductMarkedTupleSignature
import Tablet.StarProductPathRankAtMostSize

-- [TABLET NODE: StarProductConcreteUnmarkedPathNonempty]

universe u

theorem StarProductConcreteUnmarkedPathNonempty (K : Type u) [Field K] (t q k : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (v : Fin k → ProductDigraphVertex (PolarityGraph K t))
    (hv : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) v) :
    ∀ i, i < k →
      (i + 1) ∈
        (Finset.univ.filter
          (fun j : Fin k =>
            StarProductMarkedTupleSignature (PolarityGraph K t)
              (StarProductConcreteMarked K t q
                (fun _ p r => StarProductLayerChoice K t p r)) v j = true)).image
          (fun j : Fin k => j.1 + 1) →
        1 ≤ StarProductPathRankAtMostSize K t v
          (StarProductConcreteUnmarkedPsi K t v (i + 1)) i := by
-- BODY
  classical
  intro i hi _hui
  have hi_le : i ≤ k := le_of_lt hi
  let p : Fin i → ProductDigraphVertex (PolarityGraph K t) :=
    fun j => v ⟨j.1, lt_of_lt_of_le j.2 hi_le⟩
  let x : ProductDigraphVertex (PolarityGraph K t) := v ⟨i, hi⟩
  have hstepFI : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc i (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) := by
    let qfun : Fin (i + 1) → ProductDigraphVertex (PolarityGraph K t) :=
      fun j => v ⟨j.1, lt_of_lt_of_le j.2 (Nat.succ_le_iff.mpr hi)⟩
    have hqfun :
        qfun =
          @Fin.snoc i (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x := by
      rw [← Fin.snoc_init_self qfun]
      rfl
    have hqFI : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) qfun := by
      intro a b hab
      exact hv ⟨a.1, lt_of_lt_of_le a.2 (Nat.succ_le_iff.mpr hi)⟩
        ⟨b.1, lt_of_lt_of_le b.2 (Nat.succ_le_iff.mpr hi)⟩ hab
    simpa [hqfun] using hqFI
  have hrle :
      StarProductPrefixRank K t p x.val.2 ≤ t := by
    simpa [p, x] using StarProductForwardIndependentExtensionRankLe K t p x hstepFI
  have hpsi := StarProductConcreteUnmarkedPsiApply K t v hi (by simpa [p, x] using hrle)
  rw [hpsi]
  unfold StarProductPathRankAtMostSize
  simp [hi_le]
  simpa [p, x] using StarProductConcreteUnmarkedExtensionNonempty K t p x
