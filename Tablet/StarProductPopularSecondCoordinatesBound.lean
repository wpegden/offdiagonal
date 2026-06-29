import Mathlib.Tactic
import Tablet.StarProductLayerChoicePositive
import Tablet.StarProductPopularDoubleCountingBound
import Tablet.StarProductPopularSecondCoordinates
import Tablet.StarProductSubspacePointsBound

-- [TABLET NODE: StarProductPopularSecondCoordinatesBound]

universe u

theorem StarProductPopularSecondCoordinatesBound (K : Type u) [Field K] [Fintype K]
    (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t)) (r : ℕ)
    (hq : q = Fintype.card K) :
    (StarProductPopularSecondCoordinates K t q p r).card ≤
      32 * q ^ (StarProductLayerChoice K t p r) := by
-- BODY
  classical
  by_cases hUpos : 0 < (StarProductRankAtMostSet K t p r).card
  · have hZpos :
        0 < (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card :=
      StarProductLayerChoicePositive K t p r hUpos
    let popular := StarProductPopularSecondCoordinates K t q p r
    let Z := StarProductRankLayer K t p (StarProductLayerChoice K t p r)
    let W : Projectivization K (Fin (t + 1) → K) →
        Finset (Projectivization K (Fin (t + 1) → K)) :=
      fun y => StarProductSubspacePoints K t p y
    have hqposR : 0 < (q : ℝ) := by
      have hqpos : 0 < q := by
        rw [hq]
        exact Fintype.card_pos
      exact_mod_cast hqpos
    have hZposR : 0 < (Z.card : ℝ) := by
      exact_mod_cast hZpos
    have hpopular : ∀ b ∈ popular,
        ((Z.filter (fun y => b ∈ W y)).card : ℝ) ≥
          (Z.card : ℝ) / (16 * (q : ℝ)) := by
      intro b hb
      have hfilter :
          Z.filter (fun y => b ∈ W y) =
            Z.filter (fun y => Projectivization.rep b ∈ StarProductPrefixSpan K t p y) := by
        apply Finset.filter_congr
        intro y hy
        simp [W, StarProductSubspacePoints]
      rw [hfilter]
      simpa [popular, StarProductPopularSecondCoordinates, Z] using
        (Finset.mem_filter.mp hb).2
    have hfiber : ∀ y ∈ Z,
        (((W y ∩ popular).card : ℝ) ≤
          2 * (q : ℝ) ^ (StarProductLayerChoice K t p r) / (q : ℝ)) := by
      intro y hy
      have hsubset : W y ∩ popular ⊆ W y := by
        intro b hb
        exact (Finset.mem_inter.mp hb).1
      have hcard : (W y ∩ popular).card ≤ (W y).card :=
        Finset.card_le_card hsubset
      have hcardR : (((W y ∩ popular).card : ℝ) ≤ ((W y).card : ℝ)) := by
        exact_mod_cast hcard
      have hyrank :
          StarProductPrefixRank K t p y = StarProductLayerChoice K t p r := by
        simpa [Z, StarProductRankLayer] using hy
      have hdim :
          Module.finrank K (StarProductPrefixSpan K t p y) =
            StarProductLayerChoice K t p r := by
        simpa [StarProductPrefixRank] using hyrank
      exact hcardR.trans (by
        simpa [W] using
          StarProductSubspacePointsBound K t q (StarProductLayerChoice K t p r)
            p y hq hdim)
    have hreal :
        (popular.card : ℝ) ≤
          32 * (q : ℝ) ^ (StarProductLayerChoice K t p r) := by
      exact StarProductPopularDoubleCountingBound popular Z W q
        (StarProductLayerChoice K t p r) hqposR hZposR hpopular hfiber
    simpa [popular] using (by exact_mod_cast hreal)
  · have hUempty : (StarProductRankAtMostSet K t p r).card = 0 :=
      Nat.eq_zero_of_not_pos hUpos
    have hLayerEmpty : (StarProductRankLayer K t p r).card = 0 := by
      have hsubset : StarProductRankLayer K t p r ⊆ StarProductRankAtMostSet K t p r := by
        intro y hy
        have hyrank : StarProductPrefixRank K t p y = r := by
          simpa [StarProductRankLayer] using hy
        simpa [StarProductRankAtMostSet] using le_of_eq hyrank
      have hcard : (StarProductRankLayer K t p r).card ≤
          (StarProductRankAtMostSet K t p r).card :=
        Finset.card_le_card hsubset
      exact Nat.eq_zero_of_le_zero (by simpa [hUempty] using hcard)
    have hPopularEmpty :
        (StarProductPopularSecondCoordinates K t q p r).card = 0 := by
      have hsubset :
          StarProductPopularSecondCoordinates K t q p r ⊆
            StarProductRankLayer K t p r := by
        intro y hy
        exact (Finset.mem_filter.mp hy).1
      have hcard :
          (StarProductPopularSecondCoordinates K t q p r).card ≤
            (StarProductRankLayer K t p r).card :=
        Finset.card_le_card hsubset
      exact Nat.eq_zero_of_le_zero (by simpa [hLayerEmpty] using hcard)
    simp [hPopularEmpty]
