import Tablet.DigraphToGraphIndependentSetBound
import Tablet.RamseyNumber
import Tablet.SamplingKsFreeRamseyBound
import Tablet.StarProductDigraph
import Tablet.StarProductDigraphTransitiveFree
import Tablet.StarProductForwardIndependentBound
import Tablet.StarProductPolarityVertexCountLowerBound

-- [TABLET NODE: MainTheoremSamplingBridge]

universe u

theorem MainTheoremSamplingBridge (t : ℕ) (ht : 2 ≤ t) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (K : Type u) [Field K] [Fintype K]
        [Fintype (Projectivization K (Fin (t + 1) → K))]
        [Fintype (ProductDigraphVertex (PolarityGraph K t))],
        ∀ q : ℕ,
          q = Fintype.card K →
            ∀ k : ℕ,
              1 ≤ k →
                C ≤ (q : ℝ) →
                  C * (q : ℝ) * (Real.log (q : ℝ)) ^ 2 ≤ (k : ℝ) →
                    (k : ℝ) ≤ Real.exp 1 * C * (q : ℝ) ^ t →
                      (k : ℝ) * (q : ℝ) ^ (t - 1) /
                          (4 * Real.exp 1 * C) - 1 <
                        (RamseyNumber (t + 1) k : ℝ) := by
-- BODY
  classical
  rcases StarProductForwardIndependentBound t ht with ⟨C, hC_pos, hforward⟩
  refine ⟨C, hC_pos, ?_⟩
  intro K _ _ _ _ q hq k hk hCq hk_scale hp_le_one_num
  let D : Digraph (ProductDigraphVertex (PolarityGraph K t)) :=
    StarProductDigraph (PolarityGraph K t)
  have hDfree : TransitiveTournamentFree D (t + 1) := by
    simpa [D] using StarProductDigraphTransitiveFree K t ht
  rcases DigraphToGraphIndependentSetBound (D := D) (s := t + 1) (k := k)
      hDfree hk with
    ⟨G, hGKs, hGcount⟩
  let F : ℝ :=
    ((ForwardIndependentTupleCount D k : ℕ) : ℝ)
  let I : ℝ :=
    ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ)
  let A : ℝ := C * (q : ℝ) ^ t
  let p : ℝ := (k : ℝ) / (Real.exp 1 * A)
  have hk_pos_nat : 0 < k := by omega
  have hkR_pos : 0 < (k : ℝ) := by exact_mod_cast hk_pos_nat
  have hkR_nonneg : 0 ≤ (k : ℝ) := le_of_lt hkR_pos
  have hkR_ne : (k : ℝ) ≠ 0 := ne_of_gt hkR_pos
  have hq_pos_nat : 0 < q := by
    rw [hq]
    exact Fintype.card_pos
  have hqR_pos : 0 < (q : ℝ) := by exact_mod_cast hq_pos_nat
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hp_pos : 0 < p := by
    dsimp [p]
    positivity
  have hp_nonneg : 0 ≤ p := le_of_lt hp_pos
  have hp_le_one : p ≤ 1 := by
    dsimp [p, A]
    rw [div_le_iff₀ (by positivity : 0 < Real.exp 1 * (C * (q : ℝ) ^ t))]
    simpa [mul_assoc] using hp_le_one_num
  have hF_bound : F ≤ A ^ k := by
    dsimp [F, A, D]
    exact hforward K q hq k hCq hk_scale
  have hI_bound : I ≤ (Real.exp 1 / (k : ℝ)) ^ k * F := by
    dsimp [I, F]
    simpa [D] using hGcount
  have hp_rpow_eq : Real.rpow p (k : ℝ) = p ^ k := by
    exact Real.rpow_natCast p k
  have hp_pow_mul_cancel :
      p ^ k * ((Real.exp 1 / (k : ℝ)) ^ k * A ^ k) = 1 := by
    dsimp [p]
    rw [← mul_pow, ← mul_pow]
    have hmul_base :
        ((k : ℝ) / (Real.exp 1 * A)) * ((Real.exp 1 / (k : ℝ)) * A) = 1 := by
      field_simp [hkR_ne, (Real.exp_pos 1).ne', ne_of_gt hA_pos]
    rw [hmul_base]
    simp
  have hcoef_nonneg :
      0 ≤ Real.rpow p (k : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k := by
    exact mul_nonneg (Real.rpow_nonneg hp_nonneg _)
      (pow_nonneg (div_nonneg (Real.exp_pos 1).le hkR_nonneg) k)
  have hcount_sampling :
      Real.rpow p (k : ℝ) * I ≤ 1 := by
    calc
      Real.rpow p (k : ℝ) * I
          ≤ Real.rpow p (k : ℝ) *
              ((Real.exp 1 / (k : ℝ)) ^ k * F) := by
              exact mul_le_mul_of_nonneg_left hI_bound
                (Real.rpow_nonneg hp_nonneg _)
      _ = (Real.rpow p (k : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k) * F := by ring
      _ ≤ (Real.rpow p (k : ℝ) * (Real.exp 1 / (k : ℝ)) ^ k) * A ^ k := by
              exact mul_le_mul_of_nonneg_left hF_bound hcoef_nonneg
      _ = 1 := by
              rw [hp_rpow_eq]
              simpa [mul_assoc] using hp_pow_mul_cancel
  have hsampling :
      p * (Fintype.card (ProductDigraphVertex (PolarityGraph K t)) : ℝ) - 1 <
        (RamseyNumber (t + 1) k : ℝ) := by
    simpa [D, p] using
      SamplingKsFreeRamseyBound (G := G) (s := t + 1) (k := k) (p := p)
        hGKs hk hp_nonneg hp_le_one hcount_sampling
  have hvertex_lower :
      ((q : ℝ) ^ (2 * t - 1)) / 4 ≤
        (Fintype.card (ProductDigraphVertex (PolarityGraph K t)) : ℝ) :=
    StarProductPolarityVertexCountLowerBound K t q ht hq
  have hp_vertex_lower :
      (k : ℝ) * (q : ℝ) ^ (t - 1) /
            (4 * Real.exp 1 * C) ≤
        p * (Fintype.card (ProductDigraphVertex (PolarityGraph K t)) : ℝ) := by
    calc
      (k : ℝ) * (q : ℝ) ^ (t - 1) /
            (4 * Real.exp 1 * C)
          = p * (((q : ℝ) ^ (2 * t - 1)) / 4) := by
              dsimp [p, A]
              have hpow_split :
                  (q : ℝ) ^ (2 * t - 1) =
                    (q : ℝ) ^ (t - 1) * (q : ℝ) ^ t := by
                have hexp : 2 * t - 1 = (t - 1) + t := by omega
                rw [hexp, pow_add]
              rw [hpow_split]
              field_simp [(Real.exp_pos 1).ne', hC_pos.ne',
                ne_of_gt (pow_pos hqR_pos t)]
      _ ≤ p * (Fintype.card (ProductDigraphVertex (PolarityGraph K t)) : ℝ) := by
              exact mul_le_mul_of_nonneg_left hvertex_lower hp_nonneg
  linarith
