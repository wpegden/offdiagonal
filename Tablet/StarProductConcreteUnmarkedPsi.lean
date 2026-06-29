import Mathlib.Tactic
import Tablet.StarProductLayerChoiceLe

-- [TABLET NODE: StarProductConcreteUnmarkedPsi]

universe u

noncomputable def StarProductConcreteUnmarkedPsi (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {k : ℕ}
    (v : Fin k → ProductDigraphVertex (PolarityGraph K t)) : ℕ → Fin (t + 1) := by
-- BODY
  classical
  intro n
  by_cases hn : n ≤ k ∧ 0 < n
  · let i := n - 1
    have hi : i < k := by omega
    let p : Fin i → ProductDigraphVertex (PolarityGraph K t) :=
      fun j => v ⟨j.1, lt_of_lt_of_le j.2 (le_of_lt hi)⟩
    let x : ProductDigraphVertex (PolarityGraph K t) := v ⟨i, hi⟩
    let r := StarProductPrefixRank K t p x.val.2
    by_cases hr : r ≤ t
    · exact ⟨StarProductLayerChoice K t p r,
        Nat.lt_succ_of_le ((StarProductLayerChoiceLe K t p r).trans hr)⟩
    · exact ⟨0, Nat.succ_pos t⟩
  · exact ⟨0, Nat.succ_pos t⟩
