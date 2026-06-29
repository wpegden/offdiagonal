import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductIteratedShrink]

theorem StarProductIteratedShrink
    (m : ℕ) (rho N : ℝ) (U : ℕ → ℝ)
    (selected : ℕ → Prop) [DecidablePred selected]
    (hrho_nonneg : 0 ≤ rho)
    (hinit : U 0 ≤ N)
    (hselected : ∀ i, i < m → selected (i + 1) → U (i + 1) ≤ rho * U i)
    (hunselected : ∀ i, i < m → ¬ selected (i + 1) → U (i + 1) ≤ U i) :
    ∀ i, i ≤ m →
      U i ≤ N * rho ^ ((Finset.Icc 1 i).filter selected).card := by
-- BODY
  intro i hi
  induction i with
  | zero =>
      simpa using hinit
  | succ i ih =>
      have him : i < m := Nat.lt_of_succ_le hi
      by_cases hs : selected (i + 1)
      · have hcard :
          ((Finset.Icc 1 (i + 1)).filter selected).card =
            ((Finset.Icc 1 i).filter selected).card + 1 := by
          have hIcc :
              Finset.Icc 1 (i + 1) = insert (i + 1) (Finset.Icc 1 i) := by
            ext j
            simp
            omega
          rw [hIcc, Finset.filter_insert]
          simp [hs]
        calc
          U (i + 1) ≤ rho * U i := hselected i him hs
          _ ≤ rho * (N * rho ^ ((Finset.Icc 1 i).filter selected).card) := by
            exact mul_le_mul_of_nonneg_left (ih (Nat.le_of_lt him)) hrho_nonneg
          _ = N * rho ^ ((Finset.Icc 1 (i + 1)).filter selected).card := by
            rw [hcard]
            ring
      · have hcard :
          ((Finset.Icc 1 (i + 1)).filter selected).card =
            ((Finset.Icc 1 i).filter selected).card := by
          have hIcc :
              Finset.Icc 1 (i + 1) = insert (i + 1) (Finset.Icc 1 i) := by
            ext j
            simp
            omega
          rw [hIcc, Finset.filter_insert]
          simp [hs]
        calc
          U (i + 1) ≤ U i := hunselected i him hs
          _ ≤ N * rho ^ ((Finset.Icc 1 i).filter selected).card := ih (Nat.le_of_lt him)
          _ = N * rho ^ ((Finset.Icc 1 (i + 1)).filter selected).card := by
            rw [hcard]
