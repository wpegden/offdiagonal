import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductShrinkCollapseForLaterExponents]

theorem StarProductShrinkCollapseForLaterExponents (rho N : ℝ) (e : ℕ)
    (hN_nonneg : 0 ≤ N)
    (hrho_nonneg : 0 ≤ rho)
    (hrho_le_one : rho ≤ 1)
    (hbase : N * rho ^ e < 1) :
    ∀ c, e ≤ c → N * rho ^ c < 1 := by
-- BODY
  intro c hc
  have hpow_le : rho ^ c ≤ rho ^ e :=
    pow_le_pow_of_le_one hrho_nonneg hrho_le_one hc
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hpow_le hN_nonneg) hbase
