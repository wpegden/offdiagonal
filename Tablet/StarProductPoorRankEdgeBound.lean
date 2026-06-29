import Mathlib.Tactic
import Tablet.ExpanderMixingLemma
import Tablet.PolarityGraphParameters
import Tablet.StarProductLayerChoiceMax
import Tablet.StarProductPolarityParameterBounds
import Tablet.StarProductPoorExpanderMixingBound

-- [TABLET NODE: StarProductPoorRankEdgeBound]

universe u

open Classical in
theorem StarProductPoorRankEdgeBound (K : Type u) [Field K] [Fintype K]
    (t q r : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K)
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (hr : r ≤ t) :
    let V := Projectivization K (Fin (t + 1) → K)
    let G : LoopGraph V := PolarityGraph K t
    let Zell := StarProductRankLayer K t p (StarProductLayerChoice K t p r)
    let P := Finset.univ.filter (fun a : V =>
      ((Zell.filter (fun y => G a y)).card : ℝ) ≤
        (Zell.card : ℝ) / (8 * (q : ℝ)))
    let Zr := StarProductRankLayer K t p r
    ((LoopGraphEdgeCountBetween G P Zr : ℕ) : ℝ) ≤
      5000 * (q : ℝ) ^ t := by
-- BODY
  classical
  have _hr : r ≤ t := hr
  dsimp only
  let V := Projectivization K (Fin (t + 1) → K)
  let G : LoopGraph V := PolarityGraph K t
  let Zell : Finset V := StarProductRankLayer K t p (StarProductLayerChoice K t p r)
  let P : Finset V := Finset.univ.filter (fun a : V =>
    ((Zell.filter (fun y => G a y)).card : ℝ) ≤
      (Zell.card : ℝ) / (8 * (q : ℝ)))
  let Zr : Finset V := StarProductRankLayer K t p r
  change ((LoopGraphEdgeCountBetween G P Zr : ℕ) : ℝ) ≤
    5000 * (q : ℝ) ^ t
  let n := (q ^ (t + 1) - 1) / (q - 1)
  let d := (q ^ t - 1) / (q - 1)
  let a := (q ^ (t - 1) - 1) / (q - 1)
  let lambda := Real.sqrt (((d - a : ℕ) : ℝ))
  let X : ℝ := (P.card : ℝ) * (Zell.card : ℝ)
  let Y : ℝ := (P.card : ℝ) * (Zr.card : ℝ)
  let eZell : ℝ := ((LoopGraphEdgeCountBetween G P Zell : ℕ) : ℝ)
  let eZr : ℝ := ((LoopGraphEdgeCountBetween G P Zr : ℕ) : ℝ)
  have hparam :
      0 < q ∧ 2 ≤ q ∧ 0 < n ∧ 0 < d ∧
        q ^ t ≤ n ∧ n ≤ 2 * q ^ t ∧
        q ^ (t - 1) ≤ d ∧ d ≤ 2 * q ^ (t - 1) ∧
        (d - a : ℕ) = q ^ (t - 1) ∧
        lambda ^ 2 = ((q ^ (t - 1) : ℕ) : ℝ) := by
    simpa [n, d, a, lambda] using StarProductPolarityParameterBounds K t q ht hq
  rcases hparam with
    ⟨hqposNat, _hq2, hnpos, _hdpos, hn_lower, hn_upper, hd_lower, hd_upper,
      _hdiff_eq, hlambda_sq⟩
  have hqR : 0 < (q : ℝ) := by exact_mod_cast hqposNat
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
  have hparams : LoopGraphNdLambda G n d lambda := by
    simpa [G, n, d, a, lambda] using PolarityGraphParameters K t q ht hq
  have hlambda_nonneg : 0 ≤ lambda := hparams.2.2.2.2
  have hqpow_t : (q : ℝ) ^ t = (q : ℝ) ^ (t - 1) * (q : ℝ) := by
    rw [← pow_succ]
    congr 1
    omega
  have hXnonneg : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hZr_le_Zell_nat : Zr.card ≤ Zell.card := by
    change (StarProductRankLayer K t p r).card ≤
      (StarProductRankLayer K t p (StarProductLayerChoice K t p r)).card
    exact StarProductLayerChoiceMax K t p r r le_rfl
  have hZr_le_Zell : (Zr.card : ℝ) ≤ (Zell.card : ℝ) := by
    exact_mod_cast hZr_le_Zell_nat
  have hYleX : Y ≤ X := by
    dsimp [X, Y]
    exact mul_le_mul_of_nonneg_left hZr_le_Zell (Nat.cast_nonneg _)
  have hEdgeFilterSum : ∀ A B : Finset V,
      ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) =
        ∑ a ∈ A, ((B.filter (fun b : V => G a b)).card : ℝ) := by
    intro A B
    have hAdj := LoopGraphEdgeCountBetweenAdjacencyIndicator G A B
    rw [hAdj]
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hsum :
        (∑ y : V, if G x y then if y ∈ B then (1 : ℝ) else 0 else 0) =
          ((B.filter (fun y : V => G x y)).card : ℝ) := by
      calc
        (∑ y : V, if G x y then if y ∈ B then (1 : ℝ) else 0 else 0)
            = ∑ y : V, if G x y ∧ y ∈ B then (1 : ℝ) else 0 := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              by_cases hyG : G x y <;> by_cases hyB : y ∈ B <;> simp [hyG, hyB]
        _ = ((B.filter (fun y : V => G x y)).card : ℝ) := by
              rw [Finset.sum_boole]
              have hfilter :
                  (Finset.univ.filter (fun y : V => G x y ∧ y ∈ B)) =
                    B.filter (fun y : V => G x y) := by
                ext y
                simp [and_comm]
              simp [hfilter]
    rw [← hsum]
    simp [LoopGraphAdjacencyAction]
  have hpoorUpper : eZell ≤ X / (8 * (q : ℝ)) := by
    calc
      eZell = ∑ a ∈ P, ((Zell.filter (fun y => G a y)).card : ℝ) := by
        simpa [eZell] using hEdgeFilterSum P Zell
      _ ≤ ∑ a ∈ P, ((Zell.card : ℝ) / (8 * (q : ℝ))) := by
        refine Finset.sum_le_sum ?_
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ = (P.card : ℝ) * ((Zell.card : ℝ) / (8 * (q : ℝ))) := by
        simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ = X / (8 * (q : ℝ)) := by
        dsimp [X]
        ring
  have hcoeff_lower : 1 / (4 * (q : ℝ)) ≤ (d : ℝ) / (n : ℝ) := by
    rw [le_div_iff₀ hnR]
    calc
      (1 / (4 * (q : ℝ))) * (n : ℝ)
          ≤ (1 / (4 * (q : ℝ))) * (2 * (q : ℝ) ^ t) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn_upper)
              (by positivity)
      _ = (1 / 2 : ℝ) * (q : ℝ) ^ (t - 1) := by
            rw [hqpow_t]
            field_simp [ne_of_gt hqR]
            ring
      _ ≤ (q : ℝ) ^ (t - 1) := by
            have hpow_nonneg : 0 ≤ (q : ℝ) ^ (t - 1) := by positivity
            nlinarith
      _ ≤ (d : ℝ) := by exact_mod_cast hd_lower
  have hcoeff_upper : (d : ℝ) / (n : ℝ) ≤ 4 / (q : ℝ) := by
    have hmain : (q : ℝ) * (d : ℝ) ≤ 4 * (n : ℝ) := by
      calc
        (q : ℝ) * (d : ℝ)
            ≤ (q : ℝ) * (2 * (q : ℝ) ^ (t - 1)) := by
              exact mul_le_mul_of_nonneg_left (by exact_mod_cast hd_upper)
                (by positivity)
        _ = 2 * (q : ℝ) ^ t := by
              rw [hqpow_t]
              ring
        _ ≤ 2 * (n : ℝ) := by
              exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn_lower)
                (by norm_num : (0 : ℝ) ≤ 2)
        _ ≤ 4 * (n : ℝ) := by nlinarith [le_of_lt hnR]
    field_simp [ne_of_gt hqR, ne_of_gt hnR] at hmain ⊢
    nlinarith
  have hmixZell_abs :
      |eZell - ((d : ℝ) / (n : ℝ)) * X| ≤ lambda * Real.sqrt X := by
    simpa [eZell, X, mul_assoc] using
      ExpanderMixingLemma (G := G) (n := n) (d := d) (lambda := lambda)
        hparams P Zell
  have hmixLowerExact :
      ((d : ℝ) / (n : ℝ)) * X - lambda * Real.sqrt X ≤ eZell := by
    have hleft := (abs_le.mp hmixZell_abs).1
    nlinarith
  have hmixLower :
      X / (4 * (q : ℝ)) - lambda * Real.sqrt X ≤ eZell := by
    have hcoefX : X / (4 * (q : ℝ)) ≤ ((d : ℝ) / (n : ℝ)) * X := by
      calc
        X / (4 * (q : ℝ)) = (1 / (4 * (q : ℝ))) * X := by ring
        _ ≤ ((d : ℝ) / (n : ℝ)) * X :=
          mul_le_mul_of_nonneg_right hcoeff_lower hXnonneg
    nlinarith
  have hmixZr_abs :
      |eZr - ((d : ℝ) / (n : ℝ)) * Y| ≤ lambda * Real.sqrt Y := by
    simpa [eZr, Y, mul_assoc] using
      ExpanderMixingLemma (G := G) (n := n) (d := d) (lambda := lambda)
        hparams P Zr
  have hmixUpperExact :
      eZr ≤ ((d : ℝ) / (n : ℝ)) * Y + lambda * Real.sqrt Y := by
    have hright := (abs_le.mp hmixZr_abs).2
    nlinarith
  have hmixUpper :
      eZr ≤ (4 / (q : ℝ)) * Y + lambda * Real.sqrt Y := by
    have hcoefY : ((d : ℝ) / (n : ℝ)) * Y ≤ (4 / (q : ℝ)) * Y := by
      exact mul_le_mul_of_nonneg_right hcoeff_upper
        (by dsimp [Y]; exact mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
    nlinarith
  have hLsq :
      64 * (q : ℝ) ^ 2 * lambda ^ 2 ≤ 1024 * (q : ℝ) ^ (t + 1) := by
    calc
      64 * (q : ℝ) ^ 2 * lambda ^ 2
          = 64 * (q : ℝ) ^ 2 * (q : ℝ) ^ (t - 1) := by
            rw [hlambda_sq]
            norm_num
      _ = 64 * (q : ℝ) ^ (t + 1) := by
            have hexp : 2 + (t - 1) = t + 1 := by omega
            calc
              64 * (q : ℝ) ^ 2 * (q : ℝ) ^ (t - 1)
                  = 64 * ((q : ℝ) ^ 2 * (q : ℝ) ^ (t - 1)) := by ring
              _ = 64 * (q : ℝ) ^ (2 + (t - 1)) := by rw [← pow_add]
              _ = 64 * (q : ℝ) ^ (t + 1) := by rw [hexp]
      _ ≤ 1024 * (q : ℝ) ^ (t + 1) := by
            exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
  have hLsqrt :
      lambda * Real.sqrt (1024 * (q : ℝ) ^ (t + 1)) ≤
        904 * (q : ℝ) ^ t := by
    let S : ℝ := 1024 * (q : ℝ) ^ (t + 1)
    have hSnonneg : 0 ≤ S := by
      dsimp [S]
      positivity
    have hleft_nonneg : 0 ≤ lambda * Real.sqrt S := by positivity
    have hright_nonneg : 0 ≤ 904 * (q : ℝ) ^ t := by positivity
    have hsquare :
        (lambda * Real.sqrt S) ^ 2 ≤ (904 * (q : ℝ) ^ t) ^ 2 := by
      calc
        (lambda * Real.sqrt S) ^ 2
            = lambda ^ 2 * S := by
              rw [mul_pow, Real.sq_sqrt hSnonneg]
        _ = 1024 * ((q : ℝ) ^ (t - 1) * (q : ℝ) ^ (t + 1)) := by
              rw [hlambda_sq]
              dsimp [S]
              norm_num
              ring
        _ = 1024 * (q : ℝ) ^ (2 * t) := by
              have hexp : (t - 1) + (t + 1) = 2 * t := by omega
              rw [← pow_add, hexp]
        _ ≤ 904 ^ 2 * (q : ℝ) ^ (2 * t) := by
              exact mul_le_mul_of_nonneg_right (by norm_num) (by positivity)
        _ = (904 * (q : ℝ) ^ t) ^ 2 := by
              rw [mul_pow, ← pow_mul]
              ring
    have habs := (sq_le_sq.mp hsquare)
    have hleft_abs : |lambda * Real.sqrt S| = lambda * Real.sqrt S :=
      abs_of_nonneg hleft_nonneg
    have hright_abs : |904 * (q : ℝ) ^ t| = 904 * (q : ℝ) ^ t :=
      abs_of_nonneg hright_nonneg
    rw [hleft_abs, hright_abs] at habs
    simpa [S] using habs
  exact StarProductPoorExpanderMixingBound q t X Y eZell eZr lambda
    hqR hXnonneg hYleX hpoorUpper hmixLower hlambda_nonneg hLsq hmixUpper hLsqrt
