import Tablet.Preamble

-- [TABLET NODE: MainTheoremEtaBounds]

theorem MainTheoremEtaBounds (n dF dG : ℕ)
    (lambdaF lambdaG eta : ℝ)
    (hn_pos : 0 < n) (hdF_pos : 0 < dF) (hdG_pos : 0 < dG)
    (heta :
      eta = max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (hfirst_lower :
      1 / (n : ℝ) ^ 2 ≤ lambdaG ^ 2 / (dG : ℝ) ^ 2)
    (hfirst_upper : lambdaG ^ 2 / (dG : ℝ) ^ 2 ≤ 1)
    (hsecond_upper :
      lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ)) ≤ 1) :
    0 < eta ∧ 1 / (n : ℝ) ^ 2 ≤ eta ∧ eta ≤ 1 := by
-- BODY
  subst eta
  have hdF_ne : (dF : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdF_pos)
  have hdG_ne : (dG : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdG_pos)
  have hbase_pos : 0 < 1 / (n : ℝ) ^ 2 := by
    have hnR_pos : (0 : ℝ) < n := by exact_mod_cast hn_pos
    positivity
  have hlower :
      1 / (n : ℝ) ^ 2 ≤
        max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
          (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))) :=
    hfirst_lower.trans (le_max_left _ _)
  exact ⟨lt_of_lt_of_le hbase_pos hlower, hlower,
    max_le hfirst_upper hsecond_upper⟩
