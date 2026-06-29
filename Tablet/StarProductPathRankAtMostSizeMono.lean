import Mathlib.Tactic
import Tablet.StarProductPathRankAtMostSize
import Tablet.StarProductRankAtMostSetSnocSubset

-- [TABLET NODE: StarProductPathRankAtMostSizeMono]

universe u

theorem StarProductPathRankAtMostSizeMono (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {k : ℕ}
    (v : Fin k → ProductDigraphVertex (PolarityGraph K t))
    (l : Fin (t + 1)) {i : ℕ} (hi : i < k) :
    StarProductPathRankAtMostSize K t v l (i + 1) ≤
      StarProductPathRankAtMostSize K t v l i := by
-- BODY
  classical
  unfold StarProductPathRankAtMostSize
  have hi_le : i ≤ k := le_of_lt hi
  have hisucc_le : i + 1 ≤ k := Nat.succ_le_iff.mpr hi
  simp [hi_le, hisucc_le]
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
  have hsub :
      StarProductRankAtMostSet K t qfun l.1 ⊆
        StarProductRankAtMostSet K t
          (fun j : Fin i => v ⟨j.1, lt_of_lt_of_le j.2 hi_le⟩) l.1 := by
    simpa [hqfun, p, x] using StarProductRankAtMostSetSnocSubset K t p x l.1
  have hcard := Finset.card_le_card hsub
  exact_mod_cast hcard
