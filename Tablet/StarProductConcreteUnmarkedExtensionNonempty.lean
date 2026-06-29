import Mathlib.Tactic
import Tablet.StarProductLayerChoicePositive

-- [TABLET NODE: StarProductConcreteUnmarkedExtensionNonempty]

universe u

theorem StarProductConcreteUnmarkedExtensionNonempty (K : Type u) [Field K] (t : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t)) :
    let r := StarProductPrefixRank K t p x.val.2
    let ell := StarProductLayerChoice K t p r
    1 ≤ ((StarProductRankAtMostSet K t p ell).card : ℝ) := by
-- BODY
  classical
  intro r ell
  let Ur := StarProductRankAtMostSet K t p r
  let Zell := StarProductRankLayer K t p ell
  let Uell := StarProductRankAtMostSet K t p ell
  have hbmem : x.val.2 ∈ Ur := by
    simp [Ur, StarProductRankAtMostSet, r]
  have hUrpos : 0 < Ur.card := Finset.card_pos.mpr ⟨x.val.2, hbmem⟩
  have hZpos : 0 < Zell.card := by
    simpa [Zell, ell, Ur] using StarProductLayerChoicePositive K t p r hUrpos
  have hZsubU : Zell ⊆ Uell := by
    intro y hy
    have hyrank : StarProductPrefixRank K t p y = ell := by
      simpa [Zell, StarProductRankLayer] using hy
    simp [Uell, StarProductRankAtMostSet, hyrank]
  have hUpos : 0 < Uell.card := lt_of_lt_of_le hZpos (Finset.card_le_card hZsubU)
  have hOneNat : 1 ≤ Uell.card := Nat.succ_le_of_lt hUpos
  exact_mod_cast hOneNat
