import Tablet.MulticolorRamseyNumber
import Tablet.MulticolorRamseyNumberLowerBoundFromCounterexample
import Tablet.RandomHomomorphismColoringBound

-- [TABLET NODE: MulticolorTheorem]

theorem MulticolorTheorem :
    ∀ ell : ℕ, 3 ≤ ell → ∃ c : ℝ, 0 < c ∧ ∃ s0 : ℕ, ∀ s : ℕ, s0 ≤ s →
      c * Real.rpow 2 ((((ell - 1) * s : ℕ) : ℝ) / 2) ≤
        (MulticolorRamseyNumber s ell : ℝ) := by
-- BODY
  intro ell hell
  rcases RandomHomomorphismColoringBound ell hell with ⟨sR, hR⟩
  let e : ℕ := ell - 1
  let c : ℝ := (1 / 2 : ℝ) * Real.rpow 2 (-(4 * (e : ℝ)))
  have hc_pos : 0 < c := by
    dsimp [c]
    positivity
  refine ⟨c, hc_pos, max sR 9, ?_⟩
  intro s hs
  have hsR : sR ≤ s := le_trans (Nat.le_max_left sR 9) hs
  have hs9 : 9 ≤ s := le_trans (Nat.le_max_right sR 9) hs
  let X : ℝ := Real.rpow 2 (((s : ℝ) / 2 - 4) * (e : ℝ))
  let n : ℕ := Nat.floor X
  have hX_pos : 0 < X := by
    dsimp [X]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hn_le_X : (n : ℝ) ≤ X := by
    dsimp [n]
    exact Nat.floor_le hX_pos.le
  rcases hR s n hsR (by simpa [X, e] using hn_le_X) with ⟨color, hNo⟩
  have hRamsey_nat : n < MulticolorRamseyNumber s ell :=
    MulticolorRamseyNumberLowerBoundFromCounterexample s ell n (by omega) color hNo
  have hX_ge_two : 2 ≤ X := by
    have hexp_ge_one : (1 : ℝ) ≤ ((s : ℝ) / 2 - 4) * (e : ℝ) := by
      have hs_real : (9 : ℝ) ≤ s := by exact_mod_cast hs9
      have he_real : (2 : ℝ) ≤ e := by
        dsimp [e]
        exact_mod_cast (by omega : 2 ≤ ell - 1)
      nlinarith
    calc
      (2 : ℝ) = Real.rpow 2 (1 : ℝ) := by norm_num
      _ ≤ X := by
        dsimp [X]
        exact Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hexp_ge_one
  have hfloor_lower : X / 2 ≤ (n : ℝ) := by
    have hlt : X < (n : ℝ) + 1 := by
      dsimp [n]
      exact Nat.lt_floor_add_one X
    have hhalf_add : X / 2 + 1 ≤ X := by nlinarith
    linarith
  have hc_eq :
      c * Real.rpow 2 ((((ell - 1) * s : ℕ) : ℝ) / 2) = X / 2 := by
    dsimp [c, X, e]
    rw [mul_assoc]
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have hexp :
        -(4 * ((ell - 1 : ℕ) : ℝ)) + (((ell - 1) * s : ℕ) : ℝ) / 2 =
          ((s : ℝ) / 2 - 4) * ((ell - 1 : ℕ) : ℝ) := by
      have hcast : (((ell - 1) * s : ℕ) : ℝ) = ((ell - 1 : ℕ) : ℝ) * (s : ℝ) := by
        norm_num
      rw [hcast]
      ring
    rw [hexp]
    ring
  calc
    c * Real.rpow 2 ((((ell - 1) * s : ℕ) : ℝ) / 2)
        = X / 2 := hc_eq
    _ ≤ (n : ℝ) := hfloor_lower
    _ ≤ (MulticolorRamseyNumber s ell : ℝ) := by
      exact_mod_cast (Nat.le_of_lt hRamsey_nat)
