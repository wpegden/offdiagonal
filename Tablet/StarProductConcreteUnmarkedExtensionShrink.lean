import Mathlib.Tactic
import Tablet.StarProductConcreteMarked
import Tablet.StarProductForwardIndependentExtensionRankLe
import Tablet.StarProductLayerChoiceLe
import Tablet.StarProductRankAtMostCardLeSuccMulLayerChoice
import Tablet.StarProductRankAtMostSetSnocSubset
import Tablet.StarProductRankIncreasesOnGoodExtension
import Tablet.StarProductUnmarkedStepShrink

-- [TABLET NODE: StarProductConcreteUnmarkedExtensionShrink]

universe u

theorem StarProductConcreteUnmarkedExtensionShrink (K : Type u) [Field K] (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    (ht : 2 ≤ t) (hq : 0 < (q : ℝ))
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (x : ProductDigraphVertex (PolarityGraph K t))
    (hfi : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
      (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x))
    (hunmarked :
      StarProductConcreteMarked K t q
        (fun _ p r => StarProductLayerChoice K t p r) m p x = false) :
    let r := StarProductPrefixRank K t p x.val.2
    let ell := StarProductLayerChoice K t p r
    ((StarProductRankAtMostSet K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ell).card : ℝ) ≤
      (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) *
        ((StarProductRankAtMostSet K t p ell).card : ℝ) := by
-- BODY
  classical
  intro r ell
  let U := StarProductRankAtMostSet K t p ell
  let U' := StarProductRankAtMostSet K t
    (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ell
  let Z := StarProductRankLayer K t p ell
  let Neigh := Z.filter (fun y => PolarityGraph K t x.val.1 y)
  let Bad := Z.filter (fun y => Projectivization.rep x.val.2 ∈ StarProductPrefixSpan K t p y)
  let Good := Neigh \ Bad
  have hrle : r ≤ t := by
    simpa [r] using StarProductForwardIndependentExtensionRankLe K t p x hfi
  have hell_le : ell ≤ r := by
    simpa [ell] using StarProductLayerChoiceLe K t p r
  have hnot_marked :
      ¬ (r ≤ t ∧
        (StarProductPopularChild K t q
            (fun _ p r => StarProductLayerChoice K t p r) p x ∨
          StarProductPoorChild K t q
            (fun _ p r => StarProductLayerChoice K t p r) p x)) := by
    simpa [StarProductConcreteMarked, r] using hunmarked
  have hnot_pop :
      ¬ StarProductPopularChild K t q
          (fun _ p r => StarProductLayerChoice K t p r) p x := by
    intro hpop
    exact hnot_marked ⟨hrle, Or.inl hpop⟩
  have hnot_poor :
      ¬ StarProductPoorChild K t q
          (fun _ p r => StarProductLayerChoice K t p r) p x := by
    intro hpoor
    exact hnot_marked ⟨hrle, Or.inr hpoor⟩
  have hbad_lt : (Bad.card : ℝ) < (Z.card : ℝ) / (16 * (q : ℝ)) := by
    have h := hnot_pop
    dsimp [StarProductPopularChild, r, ell, Z, Bad] at h
    exact not_le.mp h
  have hneigh_gt : (Z.card : ℝ) / (8 * (q : ℝ)) < (Neigh.card : ℝ) := by
    have h := hnot_poor
    dsimp [StarProductPoorChild, r, ell, Z, Neigh] at h
    exact not_le.mp h
  have hneigh_le_good_bad_nat : Neigh.card ≤ Good.card + Bad.card := by
    simpa [Good, add_comm] using
      (Finset.card_le_card_sdiff_add_card (s := Neigh) (t := Bad))
  have hneigh_le_good_bad : (Neigh.card : ℝ) ≤ (Good.card : ℝ) + (Bad.card : ℝ) := by
    exact_mod_cast hneigh_le_good_bad_nat
  have hsplit :
      (Z.card : ℝ) / (8 * (q : ℝ)) =
        (Z.card : ℝ) / (16 * (q : ℝ)) +
          (Z.card : ℝ) / (16 * (q : ℝ)) := by
    ring
  have hgoodLower : (Good.card : ℝ) ≥ (Z.card : ℝ) / (16 * (q : ℝ)) := by
    linarith
  have hU'sub : U' ⊆ U := by
    simpa [U, U'] using StarProductRankAtMostSetSnocSubset K t p x ell
  have hgoodsub : Good ⊆ U := by
    intro y hy
    have hyNeigh : y ∈ Neigh := (Finset.mem_sdiff.mp hy).1
    have hyZ : y ∈ Z := (Finset.mem_filter.mp hyNeigh).1
    have hyrank : StarProductPrefixRank K t p y = ell := by
      simpa [Z, StarProductRankLayer] using hyZ
    simp [U, StarProductRankAtMostSet, hyrank]
  have hdisj : Disjoint U' Good := by
    rw [Finset.disjoint_left]
    intro y hyU' hyGood
    have hyNeigh : y ∈ Neigh := (Finset.mem_sdiff.mp hyGood).1
    have hyNotBad : y ∉ Bad := (Finset.mem_sdiff.mp hyGood).2
    have hyZ : y ∈ Z := (Finset.mem_filter.mp hyNeigh).1
    have hyedge : PolarityGraph K t x.val.1 y := (Finset.mem_filter.mp hyNeigh).2
    have hyrank : StarProductPrefixRank K t p y = ell := by
      simpa [Z, StarProductRankLayer] using hyZ
    have hnotspan : Projectivization.rep x.val.2 ∉ StarProductPrefixSpan K t p y := by
      intro hb
      exact hyNotBad (by simpa [Bad, Z] using ⟨hyZ, hb⟩)
    have hinc := StarProductRankIncreasesOnGoodExtension K t p x y ell hyrank hyedge hnotspan
    have hnew_le : StarProductPrefixRank K t
        (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) y ≤ ell := by
      simpa [U', StarProductRankAtMostSet] using hyU'
    omega
  have hUell_subset_Ur : U ⊆ StarProductRankAtMostSet K t p r := by
    intro y hy
    have hyell : StarProductPrefixRank K t p y ≤ ell := by
      simpa [U, StarProductRankAtMostSet] using hy
    exact by
      simp [StarProductRankAtMostSet, le_trans hyell hell_le]
  have hUcard_le_Ur :
      (U.card : ℝ) ≤ ((StarProductRankAtMostSet K t p r).card : ℝ) := by
    exact_mod_cast Finset.card_le_card hUell_subset_Ur
  have hUr_le :
      ((StarProductRankAtMostSet K t p r).card : ℝ) ≤
        ((r + 1 : ℕ) : ℝ) * (Z.card : ℝ) := by
    have h := StarProductRankAtMostCardLeSuccMulLayerChoice K t p r
    exact_mod_cast (by simpa [ell, Z] using h)
  have hr_succ_le : r + 1 ≤ 2 * t := by
    omega
  have hcoef : ((r + 1 : ℕ) : ℝ) ≤ 2 * (t : ℝ) := by
    exact_mod_cast hr_succ_le
  have hZnonneg : 0 ≤ (Z.card : ℝ) := by positivity
  have hUle : (U.card : ℝ) ≤ 2 * (t : ℝ) * (Z.card : ℝ) := by
    calc
      (U.card : ℝ) ≤ ((StarProductRankAtMostSet K t p r).card : ℝ) := hUcard_le_Ur
      _ ≤ ((r + 1 : ℕ) : ℝ) * (Z.card : ℝ) := hUr_le
      _ ≤ (2 * (t : ℝ)) * (Z.card : ℝ) := mul_le_mul_of_nonneg_right hcoef hZnonneg
      _ = 2 * (t : ℝ) * (Z.card : ℝ) := by ring
  have htR : 0 < (t : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by decide : 0 < 2) ht)
  simpa [U, U', Z, Good] using
    StarProductUnmarkedStepShrink U U' Z Good t q htR hq hU'sub hgoodsub hdisj
      hgoodLower hUle
