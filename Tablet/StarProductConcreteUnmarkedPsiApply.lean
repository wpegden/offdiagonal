import Mathlib.Tactic
import Tablet.StarProductConcreteUnmarkedPsi

-- [TABLET NODE: StarProductConcreteUnmarkedPsiApply]

universe u

theorem StarProductConcreteUnmarkedPsiApply (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {k i : ℕ}
    (v : Fin k → ProductDigraphVertex (PolarityGraph K t))
    (hi : i < k)
    (hrle :
      StarProductPrefixRank K t
        (fun j : Fin i => v ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt hi)⟩)
        (v ⟨i, hi⟩).val.2 ≤ t) :
    StarProductConcreteUnmarkedPsi K t v (i + 1) =
      ⟨StarProductLayerChoice K t
          (fun j : Fin i => v ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt hi)⟩)
          (StarProductPrefixRank K t
            (fun j : Fin i => v ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt hi)⟩)
            (v ⟨i, hi⟩).val.2),
        Nat.lt_succ_of_le
          ((StarProductLayerChoiceLe K t
            (fun j : Fin i => v ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt hi)⟩)
            (StarProductPrefixRank K t
              (fun j : Fin i => v ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt hi)⟩)
              (v ⟨i, hi⟩).val.2)).trans hrle)⟩ := by
-- BODY
  classical
  unfold StarProductConcreteUnmarkedPsi
  simp [hi, hrle]
