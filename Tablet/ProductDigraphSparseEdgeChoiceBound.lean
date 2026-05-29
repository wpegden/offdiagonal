import Tablet.SparseNeighborhoodSetBound

-- [TABLET NODE: ProductDigraphSparseEdgeChoiceBound]

universe u

theorem ProductDigraphSparseEdgeChoiceBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (n dF dG : ℕ) (lambdaF lambdaG eta : ℝ)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hn : 0 < n) (hdF : 0 < dF) (hdG : 0 < dG)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (A B : Finset V)
    (hA : ∀ u : V, u ∈ A ↔
      ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ) ≤
        ((dG : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ))) :
    ((LoopGraphEdgeCountBetween F A B : ℕ) : ℝ) ≤
      ((8 : ℝ) * eta) * (((dF * n : ℕ) : ℝ)) := by
-- BODY
  classical
  let X : ℝ := (A.card : ℝ) * (B.card : ℝ)
  let m : ℝ := ((LoopGraphEdgeCountBetween F A B : ℕ) : ℝ)
  let q : ℝ := ((dF : ℝ) / (n : ℝ)) * X
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdFR : (0 : ℝ) < (dF : ℝ) := by exact_mod_cast hdF
  have hdGR : (0 : ℝ) < (dG : ℝ) := by exact_mod_cast hdG
  have hX_nonneg : 0 ≤ X := by
    dsimp [X]
    positivity
  have hSparse :
      X ≤ (4 : ℝ) * lambdaG ^ 2 / (dG : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
    simpa [X] using
      (SparseNeighborhoodSetBound G n dG lambdaG hG hn hdG A B hA)
  have hmix := ExpanderMixingLemma (G := F) (n := n) (d := dF)
    (lambda := lambdaF) hF A B
  have hmix_q : |m - q| ≤ lambdaF * Real.sqrt X := by
    simpa [m, q, X, mul_assoc] using hmix
  have hm_le_q :
      m ≤ q + lambdaF * Real.sqrt X := by
    have hle_abs : m - q ≤ |m - q| := le_abs_self _
    linarith
  have heta_left :
      lambdaG ^ 2 / (dG : ℝ) ^ 2 ≤ eta := by
    rw [heta]
    exact le_max_left _ _
  have heta_right :
      lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ)) ≤ eta := by
    rw [heta]
    exact le_max_right _ _
  have heta_nonneg : 0 ≤ eta := by
    have hfirst_nonneg :
        0 ≤ lambdaG ^ 2 / (dG : ℝ) ^ 2 := by
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    exact le_trans hfirst_nonneg heta_left
  have hq_le :
      q ≤ (4 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
    have hscale_nonneg : 0 ≤ (dF : ℝ) / (n : ℝ) := by
      positivity
    have hmul := mul_le_mul_of_nonneg_left hSparse hscale_nonneg
    have hq_sparse :
        q ≤ ((dF : ℝ) / (n : ℝ)) *
            ((4 : ℝ) * lambdaG ^ 2 / (dG : ℝ) ^ 2 * (n : ℝ) ^ 2) := by
      simpa [q, mul_assoc] using hmul
    have hrewrite :
        ((dF : ℝ) / (n : ℝ)) *
            ((4 : ℝ) * lambdaG ^ 2 / (dG : ℝ) ^ 2 * (n : ℝ) ^ 2) =
          (4 : ℝ) * (lambdaG ^ 2 / (dG : ℝ) ^ 2) * (dF : ℝ) * (n : ℝ) := by
      field_simp [hnR.ne']
    have hscale_eta :
        (4 : ℝ) * (lambdaG ^ 2 / (dG : ℝ) ^ 2) * (dF : ℝ) * (n : ℝ) ≤
          (4 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
      have hnonneg : 0 ≤ (4 : ℝ) * (dF : ℝ) * (n : ℝ) := by
        positivity
      have hscaled := mul_le_mul_of_nonneg_right heta_left hnonneg
      nlinarith
    calc
      q ≤ ((dF : ℝ) / (n : ℝ)) *
            ((4 : ℝ) * lambdaG ^ 2 / (dG : ℝ) ^ 2 * (n : ℝ) ^ 2) := hq_sparse
      _ = (4 : ℝ) * (lambdaG ^ 2 / (dG : ℝ) ^ 2) * (dF : ℝ) * (n : ℝ) := hrewrite
      _ ≤ (4 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := hscale_eta
  have hsqrt_le :
      Real.sqrt X ≤ ((2 : ℝ) * lambdaG * (n : ℝ)) / (dG : ℝ) := by
    have hlambdaG_nonneg : 0 ≤ lambdaG := hG.2.2.2.2
    have hrhs_nonneg :
        0 ≤ ((2 : ℝ) * lambdaG * (n : ℝ)) / (dG : ℝ) := by
      positivity
    rw [Real.sqrt_le_left hrhs_nonneg]
    have hsq_eq :
        (((2 : ℝ) * lambdaG * (n : ℝ)) / (dG : ℝ)) ^ 2 =
          (4 : ℝ) * lambdaG ^ 2 / (dG : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      field_simp [hdGR.ne']
      ring
    simpa [hsq_eq] using hSparse
  have hterm_le :
      lambdaF * Real.sqrt X ≤ (4 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
    have hlambdaF_nonneg : 0 ≤ lambdaF := hF.2.2.2.2
    have hmul := mul_le_mul_of_nonneg_left hsqrt_le hlambdaF_nonneg
    have hden_pos : 0 < (dF : ℝ) * (dG : ℝ) := by
      positivity
    have hprod_le :
        lambdaF * lambdaG ≤ eta * ((dF : ℝ) * (dG : ℝ)) := by
      rw [div_le_iff₀ hden_pos] at heta_right
      exact heta_right
    have hscale_nonneg : 0 ≤ (2 : ℝ) * (n : ℝ) / (dG : ℝ) := by
      positivity
    have hscaled := mul_le_mul_of_nonneg_right hprod_le hscale_nonneg
    have htarget2 :
        lambdaF * (((2 : ℝ) * lambdaG * (n : ℝ)) / (dG : ℝ)) ≤
          (2 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
      calc
        lambdaF * (((2 : ℝ) * lambdaG * (n : ℝ)) / (dG : ℝ))
            = (lambdaF * lambdaG) * ((2 : ℝ) * (n : ℝ) / (dG : ℝ)) := by
              field_simp [hdGR.ne']
        _ ≤ eta * ((dF : ℝ) * (dG : ℝ)) *
              ((2 : ℝ) * (n : ℝ) / (dG : ℝ)) := hscaled
        _ = (2 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
              field_simp [hdGR.ne']
    have htwo_four :
        (2 : ℝ) * eta * (dF : ℝ) * (n : ℝ) ≤
          (4 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
      have hnonneg : 0 ≤ eta * (dF : ℝ) * (n : ℝ) := by
        positivity
      nlinarith
    exact le_trans (le_trans hmul htarget2) htwo_four
  have hm_real :
      m ≤ (8 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
    calc
      m ≤ q + lambdaF * Real.sqrt X := hm_le_q
      _ ≤ (4 : ℝ) * eta * (dF : ℝ) * (n : ℝ) +
          (4 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
            exact add_le_add hq_le hterm_le
      _ = (8 : ℝ) * eta * (dF : ℝ) * (n : ℝ) := by
            ring
  simpa [m, Nat.cast_mul, mul_assoc] using hm_real
