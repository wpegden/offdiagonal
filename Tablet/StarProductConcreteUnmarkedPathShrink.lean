import Mathlib.Tactic
import Tablet.StarProductConcreteMarked
import Tablet.StarProductConcreteUnmarkedExtensionShrink
import Tablet.StarProductConcreteUnmarkedPsiApply
import Tablet.StarProductForwardIndependentExtensionRankLe
import Tablet.StarProductMarkedTupleSignature
import Tablet.StarProductPathRankAtMostSize

-- [TABLET NODE: StarProductConcreteUnmarkedPathShrink]

universe u

theorem StarProductConcreteUnmarkedPathShrink (K : Type u) [Field K] (t q k : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : 0 < (q : ℝ))
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
        StarProductPathRankAtMostSize K t v
            (StarProductConcreteUnmarkedPsi K t v (i + 1)) (i + 1) ≤
          (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) *
            StarProductPathRankAtMostSize K t v
              (StarProductConcreteUnmarkedPsi K t v (i + 1)) i := by
-- BODY
  classical
  intro i hi hui
  have hi_le : i ≤ k := le_of_lt hi
  have hisucc_le : i + 1 ≤ k := Nat.succ_le_iff.mpr hi
  let p : Fin i → ProductDigraphVertex (PolarityGraph K t) :=
    fun j => v ⟨j.1, lt_of_lt_of_le j.2 hi_le⟩
  let x : ProductDigraphVertex (PolarityGraph K t) := v ⟨i, hi⟩
  let qfun : Fin (i + 1) → ProductDigraphVertex (PolarityGraph K t) :=
    fun j => v ⟨j.1, lt_of_lt_of_le j.2 hisucc_le⟩
  have hqfun :
      qfun =
        @Fin.snoc i (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x := by
    rw [← Fin.snoc_init_self qfun]
    rfl
  have hstepFI : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc i (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) := by
    have hqFI : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) qfun := by
      intro a b hab
      exact hv ⟨a.1, lt_of_lt_of_le a.2 hisucc_le⟩
        ⟨b.1, lt_of_lt_of_le b.2 hisucc_le⟩ hab
    simpa [hqfun] using hqFI
  have hsig :
      StarProductMarkedTupleSignature (PolarityGraph K t)
        (StarProductConcreteMarked K t q
          (fun _ p r => StarProductLayerChoice K t p r)) v ⟨i, hi⟩ = true := by
    rcases Finset.mem_image.mp hui with ⟨j, hj, hji⟩
    have hval : j.1 = i := by
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hji)
    have hj_eq : j = ⟨i, hi⟩ := Fin.ext hval
    have hj_sig := (Finset.mem_filter.mp hj).2
    simpa [hj_eq] using hj_sig
  have hunmarked :
      StarProductConcreteMarked K t q
        (fun _ p r => StarProductLayerChoice K t p r) i p x = false := by
    have hsig' := hsig
    dsimp [StarProductMarkedTupleSignature] at hsig'
    simpa [p, x] using hsig'
  have hrle :
      StarProductPrefixRank K t p x.val.2 ≤ t := by
    simpa [p, x] using StarProductForwardIndependentExtensionRankLe K t p x hstepFI
  have hpsi := StarProductConcreteUnmarkedPsiApply K t v hi (by simpa [p, x] using hrle)
  rw [hpsi]
  unfold StarProductPathRankAtMostSize
  simp [hi_le, hisucc_le]
  simpa [p, x, qfun, hqfun] using
    StarProductConcreteUnmarkedExtensionShrink K t q ht hq p x hstepFI hunmarked
