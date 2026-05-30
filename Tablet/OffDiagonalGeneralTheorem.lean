import Tablet.ComplementPolarityPairHsFree
import Tablet.OffDiagonalGeneralDyadicScale
import Tablet.PolarityGraphParameters
import Tablet.RamseyFromGraphPair

-- [TABLET NODE: OffDiagonalGeneralTheorem]

theorem OffDiagonalGeneralTheorem :
    ∀ delta : ℝ, 0 < delta → ∃ L : ℕ, ∀ s k : ℕ, L ≤ s → L * s ≤ k →
      Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta) * (s : ℝ)) ≤
        (RamseyNumber s k : ℝ) := by
-- BODY
  intro delta hdelta
  let delta0 : ℝ := min (delta / 2) (1 / 20)
  have hdelta0_pos : 0 < delta0 := by
    dsimp [delta0]
    exact lt_min (half_pos hdelta) (by norm_num)
  have hdelta0_le_delta : delta0 ≤ delta := by
    dsimp [delta0]
    exact (min_le_left _ _).trans (by linarith)
  have hdelta0_lt_tenth : delta0 < 1 / 10 := by
    dsimp [delta0]
    have hle : min (delta / 2) (1 / 20 : ℝ) ≤ 1 / 20 := min_le_right _ _
    linarith
  have hnormalized :
      ∃ L0 : ℕ, ∀ s k : ℕ, L0 ≤ s → L0 * s ≤ k →
        Real.rpow ((k : ℝ) / (s : ℝ)) ((1 - delta0) * (s : ℝ)) ≤
          (RamseyNumber s k : ℝ) := by
    rcases OffDiagonalGeneralDyadicScale delta0 hdelta0_pos hdelta0_lt_tenth with
      ⟨X0, hscale⟩
    rcases exists_nat_ge X0 with ⟨Lx, hX0_le_Lx⟩
    refine ⟨max Lx 1, ?_⟩
    intro s k hs hk
    let x : ℝ := (k : ℝ) / (s : ℝ)
    have hs_one : 1 ≤ s := (Nat.le_max_right Lx 1).trans hs
    have hs_pos_nat : 0 < s := by omega
    have hs_pos_real : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
    have hmax_le_x : ((max Lx 1 : ℕ) : ℝ) ≤ x := by
      dsimp [x]
      rw [le_div_iff₀ hs_pos_real]
      exact_mod_cast hk
    have hLx_le_max : (Lx : ℝ) ≤ ((max Lx 1 : ℕ) : ℝ) := by
      exact_mod_cast Nat.le_max_left Lx 1
    have hX0_le_x : X0 ≤ x := hX0_le_Lx.trans (hLx_le_max.trans hmax_le_x)
    rcases hscale x hX0_le_x with
      ⟨m, hm_pos, hcard, hq_le, hy_le_twoq, hq_lower, hx_ge_one,
        hlogx_ge_one, hlogq_le_logx, hlogq_pos⟩
    -- Remaining work: use this dyadic `q = 2^m` package to instantiate the
    -- polarity construction and apply `RamseyFromGraphPair`.
    sorry
  rcases hnormalized with ⟨L0, hL0⟩
  refine ⟨max L0 1, ?_⟩
  intro s k hs hk
  have hL0s : L0 ≤ s := (Nat.le_max_left L0 1).trans hs
  have hL0sk : L0 * s ≤ k := by
    exact (Nat.mul_le_mul_right s (Nat.le_max_left L0 1)).trans hk
  have hs_one : 1 ≤ s := (Nat.le_max_right L0 1).trans hs
  have hs_pos_nat : 0 < s := by omega
  have hs_pos_real : 0 < (s : ℝ) := by exact_mod_cast hs_pos_nat
  have hbase_ge_one : (1 : ℝ) ≤ (k : ℝ) / (s : ℝ) := by
    have hs_le_k : s ≤ k := by
      have hs_le_max_mul : s ≤ max L0 1 * s := by
        simpa [one_mul] using Nat.mul_le_mul_right s (Nat.le_max_right L0 1)
      exact hs_le_max_mul.trans hk
    rw [le_div_iff₀ hs_pos_real]
    simpa using (by exact_mod_cast hs_le_k : (s : ℝ) ≤ (k : ℝ))
  have hexponent_le :
      (1 - delta) * (s : ℝ) ≤ (1 - delta0) * (s : ℝ) := by
    have hs_nonneg : 0 ≤ (s : ℝ) := by positivity
    nlinarith
  exact (Real.rpow_le_rpow_of_exponent_le hbase_ge_one hexponent_le).trans
    (hL0 s k hL0s hL0sk)
