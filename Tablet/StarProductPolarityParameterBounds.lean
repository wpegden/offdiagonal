import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductPolarityParameterBounds]

universe u

theorem StarProductPolarityParameterBounds (K : Type u) [Field K] [Fintype K]
    (t q : ℕ) (ht : 2 ≤ t) (hq : q = Fintype.card K) :
    let n := (q ^ (t + 1) - 1) / (q - 1)
    let d := (q ^ t - 1) / (q - 1)
    let a := (q ^ (t - 1) - 1) / (q - 1)
    let lambda := Real.sqrt (((d - a : ℕ) : ℝ))
    0 < q ∧ 2 ≤ q ∧ 0 < n ∧ 0 < d ∧
      q ^ t ≤ n ∧ n ≤ 2 * q ^ t ∧
      q ^ (t - 1) ≤ d ∧ d ≤ 2 * q ^ (t - 1) ∧
      (d - a : ℕ) = q ^ (t - 1) ∧
      lambda ^ 2 = ((q ^ (t - 1) : ℕ) : ℝ) := by
-- BODY
  dsimp
  have hq2 : 2 ≤ q := by
    rw [hq]
    exact Nat.succ_le_iff.mpr Fintype.one_lt_card
  let n := (q ^ (t + 1) - 1) / (q - 1)
  let d := (q ^ t - 1) / (q - 1)
  let a := (q ^ (t - 1) - 1) / (q - 1)
  let lambda := Real.sqrt (((d - a : ℕ) : ℝ))
  have hn_sum : n = ∑ i ∈ Finset.range (t + 1), q ^ i := by
    dsimp [n]
    rw [Nat.geomSum_eq hq2]
  have hd_sum : d = ∑ i ∈ Finset.range t, q ^ i := by
    dsimp [d]
    rw [Nat.geomSum_eq hq2]
  have ha_sum : a = ∑ i ∈ Finset.range (t - 1), q ^ i := by
    dsimp [a]
    rw [Nat.geomSum_eq hq2]
  have hn_eq : n = d + q ^ t := by
    rw [hn_sum, hd_sum, Finset.sum_range_succ]
  have hd_eq : d = a + q ^ (t - 1) := by
    have ht_eq : t = (t - 1) + 1 := by omega
    have hd_sum' : d = ∑ i ∈ Finset.range ((t - 1) + 1), q ^ i := by
      rw [← ht_eq]
      exact hd_sum
    rw [hd_sum', ha_sum, Finset.sum_range_succ]
  have hdiff_eq : (d - a : ℕ) = q ^ (t - 1) := by omega
  have hn_lower : q ^ t ≤ n := by omega
  have hd_lower : q ^ (t - 1) ≤ d := by omega
  have hn_upper : n ≤ 2 * q ^ t := by
    rw [hn_eq]
    have hprev_lt : d < q ^ t := by
      rw [hd_sum]
      exact Nat.geomSum_lt hq2 (by
        intro k hk
        simpa using Finset.mem_range.mp hk)
    omega
  have hd_upper : d ≤ 2 * q ^ (t - 1) := by
    rw [hd_eq]
    have hprev_lt : a < q ^ (t - 1) := by
      rw [ha_sum]
      exact Nat.geomSum_lt hq2 (by
        intro k hk
        simpa using Finset.mem_range.mp hk)
    omega
  have hn_pos : 0 < n := lt_of_lt_of_le (pow_pos (by omega : 0 < q) t) hn_lower
  have hd_pos : 0 < d :=
    lt_of_lt_of_le (pow_pos (by omega : 0 < q) (t - 1)) hd_lower
  have hlambda_sq :
      lambda ^ 2 = ((q ^ (t - 1) : ℕ) : ℝ) := by
    dsimp [lambda]
    rw [hdiff_eq]
    exact Real.sq_sqrt (Nat.cast_nonneg _)
  exact ⟨by omega, hq2, hn_pos, hd_pos, hn_lower, hn_upper, hd_lower, hd_upper,
    hdiff_eq, hlambda_sq⟩
