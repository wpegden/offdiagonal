import Mathlib.Tactic
import Tablet.StarProductConcretePathUnmarkedCertificate
import Tablet.StarProductConcreteUnmarkedPathNonempty
import Tablet.StarProductConcreteUnmarkedPathShrink
import Tablet.StarProductPathRankAtMostSizeMono
import Tablet.PolarityGraphParameters
import Tablet.StarProductPolarityParameterBounds
import Tablet.StarProductShrinkCollapseForLaterExponents
import Tablet.StarProductShrinkThresholdCollapse

-- [TABLET NODE: StarProductConcretePathWeightBound]

universe u

theorem StarProductConcretePathWeightBound (K : Type u)
    [Field K] [Fintype K] (t q k w : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    (v : Fin k → ProductDigraphVertex (PolarityGraph K t))
    (hv : ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) v)
    (hfactor :
      (1 - 1 / (32 * (t : ℝ) * (q : ℝ))) ^ (w / (t + 1) - 1) <
        1 / (4 * (q : ℝ) ^ t)) :
    BinarySequenceWeight
      (StarProductMarkedTupleSignature (PolarityGraph K t)
        (StarProductConcreteMarked K t q
          (fun _ p r => StarProductLayerChoice K t p r)) v) ≤ w := by
-- BODY
  classical
  let rho : ℝ := 1 - 1 / (32 * (t : ℝ) * (q : ℝ))
  let N : ℝ := 2 * (q : ℝ) ^ t
  obtain ⟨hq_pos_nat, hq_two, _hn_pos, _hd_pos, _hn_lower, hn_upper,
      _hd_lower, _hd_upper, _hdiff, _hlambda⟩ :=
    StarProductPolarityParameterBounds K t q ht hq
  have hq_pos_real : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have ht_pos_real : 0 < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) ht)
  have hden_pos : 0 < 32 * (t : ℝ) * (q : ℝ) := by positivity
  have hden_ge_one : 1 ≤ 32 * (t : ℝ) * (q : ℝ) := by
    have ht_two_real : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have hq_two_real : (2 : ℝ) ≤ q := by exact_mod_cast hq_two
    nlinarith
  have hrec_le_one : 1 / (32 * (t : ℝ) * (q : ℝ)) ≤ 1 := by
    rw [div_le_one hden_pos]
    exact hden_ge_one
  have hrho_nonneg : 0 ≤ rho := by
    dsimp [rho]
    linarith
  have hrho_le_one : rho ≤ 1 := by
    dsimp [rho]
    have hrec_nonneg : 0 ≤ 1 / (32 * (t : ℝ) * (q : ℝ)) := by positivity
    linarith
  have hinit : ∀ l, StarProductPathRankAtMostSize K t v l 0 ≤ N := by
    intro l
    have hcard_le :
        (StarProductRankAtMostSet K t
          (fun j : Fin 0 => v ⟨j.1, by omega⟩) l.1).card ≤
          Fintype.card (Projectivization K (Fin (t + 1) → K)) :=
      Finset.card_le_univ _
    have hparams : LoopGraphNdLambda (PolarityGraph K t)
        ((q ^ (t + 1) - 1) / (q - 1))
        ((q ^ t - 1) / (q - 1))
        (Real.sqrt
          ((((q ^ t - 1) / (q - 1)) -
            ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ)) := by
      simpa using PolarityGraphParameters K t q ht hq
    have hcardV :
        Fintype.card (Projectivization K (Fin (t + 1) → K)) =
          ((q ^ (t + 1) - 1) / (q - 1)) := hparams.1
    have hcard_le_n :
        (StarProductRankAtMostSet K t
          (fun j : Fin 0 => v ⟨j.1, by omega⟩) l.1).card ≤
          ((q ^ (t + 1) - 1) / (q - 1)) := by
      simpa [hcardV] using hcard_le
    have hcard_le_q :
        (StarProductRankAtMostSet K t
          (fun j : Fin 0 => v ⟨j.1, by omega⟩) l.1).card ≤
          2 * q ^ t := hcard_le_n.trans hn_upper
    have hcard_le_q_real :
        ((StarProductRankAtMostSet K t
          (fun j : Fin 0 => v ⟨j.1, by omega⟩) l.1).card : ℝ) ≤
          (2 * q ^ t : ℕ) := by
      exact_mod_cast hcard_le_q
    unfold StarProductPathRankAtMostSize
    simpa [N] using hcard_le_q_real
  have hN_le : N ≤ 2 * (q : ℝ) ^ t := by rfl
  have hN_nonneg : 0 ≤ N := by positivity
  have hqpow_pos : 0 < (q : ℝ) ^ t := by positivity
  have hbase : N * rho ^ (w / (t + 1) - 1) < 1 := by
    exact StarProductShrinkThresholdCollapse q t (w / (t + 1) - 1) N rho
      hN_le (pow_nonneg hrho_nonneg _) hqpow_pos (by simpa [rho] using hfactor)
  have hcollapse : ∀ c, w / (t + 1) - 1 ≤ c → N * rho ^ c < 1 :=
    StarProductShrinkCollapseForLaterExponents rho N (w / (t + 1) - 1)
      hN_nonneg hrho_nonneg hrho_le_one hbase
  exact
    StarProductConcretePathUnmarkedCertificate K t q k w
      (fun _ p r => StarProductLayerChoice K t p r) v rho N
      (StarProductConcreteUnmarkedPsi K t v)
      hrho_nonneg hinit
      (by
        simpa [rho] using StarProductConcreteUnmarkedPathShrink K t q k ht hq_pos_real v hv)
      (by
        intro l i hi _hnot
        exact StarProductPathRankAtMostSizeMono K t v l hi)
      (by
        exact StarProductConcreteUnmarkedPathNonempty K t q k v hv)
      hcollapse
