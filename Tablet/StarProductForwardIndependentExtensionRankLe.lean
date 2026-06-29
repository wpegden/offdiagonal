import Mathlib.Tactic
import Tablet.StarProductFullRankNoForwardIndependentExtension

-- [TABLET NODE: StarProductForwardIndependentExtensionRankLe]

universe u

theorem StarProductForwardIndependentExtensionRankLe (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (hfi : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x)) :
    StarProductPrefixRank K t p x.val.2 ≤ t := by
-- BODY
  classical
  let r := StarProductPrefixRank K t p x.val.2
  have hrle_succ : r ≤ t + 1 := by
    dsimp [r, StarProductPrefixRank]
    simpa [Module.finrank_fintype_fun_eq_card] using
      (Submodule.finrank_le (StarProductPrefixSpan K t p x.val.2))
  by_contra hnot
  have hr_eq : r = t + 1 := by omega
  exact (StarProductFullRankNoForwardIndependentExtension K t p x.val.2 x rfl
    (by simpa [r] using hr_eq)) hfi
