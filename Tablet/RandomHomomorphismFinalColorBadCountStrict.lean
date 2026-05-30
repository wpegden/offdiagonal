import Mathlib.Data.Nat.Choose.Bounds
import Tablet.RandomHomomorphismFinalColorArithmetic
import Tablet.RandomHomomorphismFinalColorBadCountUpper

-- [TABLET NODE: RandomHomomorphismFinalColorBadCountStrict]

theorem RandomHomomorphismFinalColorBadCountStrict {W : Type} [Fintype W]
    (D : Digraph W) (s ell n : ℕ) (hell : 3 ≤ ell) (hs4 : 4 ≤ s) (hsn : s ≤ n)
    (hW : ((2 ^ (2 * s - 4) : ℕ) : ℝ) < (Fintype.card W : ℝ))
    (hF : ((ForwardIndependentTupleCount D s : ℕ) : ℝ) ≤
      Real.rpow 2 ((3 / 2 : ℝ) * (s : ℝ) ^ 2))
    (hn : (n : ℝ) ≤
      Real.rpow 2 (((s : ℝ) / 2 - 4) * ((ell - 1 : ℕ) : ℝ))) :
    let Ω := Fin (ell - 1) → Fin n → W
    let Bad : Ω → Prop := fun phi =>
      ∃ S : Finset (Fin n), S.card = s ∧
        ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v →
          RandomHomomorphismColoring D ell n (by omega) phi (Sym2.mk u v) =
            (⟨ell - 1, by omega⟩ : Fin ell)
    Fintype.card {phi : Ω // Bad phi} < Fintype.card Ω := by
-- BODY
  classical
  intro Ω Bad
  let e : ℕ := ell - 1
  let N : ℕ := Fintype.card W
  let F : ℕ := ForwardIndependentTupleCount D s
  have he_pos : 0 < e := by
    dsimp [e]
    omega
  have hs_pos : 0 < s := by omega
  have hn_pos_nat : 0 < n := lt_of_lt_of_le hs_pos hsn
  have hN_pos_nat : 0 < N := by
    have hbase_nonneg : (0 : ℝ) ≤ ((2 ^ (2 * s - 4) : ℕ) : ℝ) := by positivity
    have hN_pos_real : (0 : ℝ) < (N : ℝ) := lt_of_le_of_lt hbase_nonneg (by simpa [N] using hW)
    exact_mod_cast hN_pos_real
  have hupper_nat :
      Fintype.card {phi : Ω // Bad phi} ≤
        Nat.choose n s * F ^ e * N ^ (e * (n - s)) := by
    simpa [Ω, Bad, e, N, F] using RandomHomomorphismFinalColorBadCountUpper D s ell n hell
  have hchoose_real : ((Nat.choose n s : ℕ) : ℝ) ≤ (n : ℝ) ^ s := by
    exact_mod_cast Nat.choose_le_pow n s
  have hFpow_real :
      ((F ^ e : ℕ) : ℝ) ≤
        Real.rpow 2 (((3 / 2 : ℝ) * (s : ℝ) ^ 2) * (e : ℝ)) := by
    calc
      ((F ^ e : ℕ) : ℝ) = (F : ℝ) ^ e := by norm_num
      _ ≤ (Real.rpow 2 ((3 / 2 : ℝ) * (s : ℝ) ^ 2)) ^ e := by
        exact pow_le_pow_left₀ (by positivity : 0 ≤ (F : ℝ)) (by simpa [F] using hF) e
      _ = Real.rpow 2 (((3 / 2 : ℝ) * (s : ℝ) ^ 2) * (e : ℝ)) := by
        calc
          (Real.rpow 2 ((3 / 2 : ℝ) * (s : ℝ) ^ 2)) ^ e
              = Real.rpow (Real.rpow 2 ((3 / 2 : ℝ) * (s : ℝ) ^ 2)) (e : ℝ) := by
                exact (Real.rpow_natCast _ e).symm
          _ = Real.rpow 2 (((3 / 2 : ℝ) * (s : ℝ) ^ 2) * (e : ℝ)) := by
                exact (Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
                  ((3 / 2 : ℝ) * (s : ℝ) ^ 2) (e : ℝ)).symm
  let C : ℝ := Real.rpow 2 (((-(s : ℝ) ^ 2 / 2 + 4 * (s : ℝ)) * (e : ℝ)))
  have hC_pos : 0 < C := by
    dsimp [C]
    exact Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _
  have hlower_pow :
      Real.rpow 2 ((((2 * s - 4 : ℕ) : ℝ) * ((s * e : ℕ) : ℝ))) <
        (N : ℝ) ^ (s * e) := by
    have hbase_cast :
        (((2 ^ (2 * s - 4) : ℕ) : ℝ)) =
          Real.rpow 2 (((2 * s - 4 : ℕ) : ℝ)) := by
      norm_num [Real.rpow_natCast]
    have hbase_lt : Real.rpow 2 (((2 * s - 4 : ℕ) : ℝ)) < (N : ℝ) := by
      simpa [N, hbase_cast] using hW
    have hexp_pos : s * e ≠ 0 := by
      exact Nat.mul_ne_zero hs_pos.ne' he_pos.ne'
    calc
      Real.rpow 2 ((((2 * s - 4 : ℕ) : ℝ) * ((s * e : ℕ) : ℝ)))
          = (Real.rpow 2 (((2 * s - 4 : ℕ) : ℝ))) ^ (s * e) := by
            calc
              Real.rpow 2 ((((2 * s - 4 : ℕ) : ℝ) * ((s * e : ℕ) : ℝ)))
                  = Real.rpow (Real.rpow 2 (((2 * s - 4 : ℕ) : ℝ))) ((s * e : ℕ) : ℝ) := by
                    exact Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)
                      (((2 * s - 4 : ℕ) : ℝ)) (((s * e : ℕ) : ℝ))
              _ = (Real.rpow 2 (((2 * s - 4 : ℕ) : ℝ))) ^ (s * e) := by
                    exact Real.rpow_natCast _ (s * e)
      _ < (N : ℝ) ^ (s * e) := by
            exact pow_lt_pow_left₀ hbase_lt
              (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hexp_pos
  have hpow_factor :
      Real.rpow 2 (((3 / 2 : ℝ) * (s : ℝ) ^ 2) * (e : ℝ)) <
        (N : ℝ) ^ (s * e) * C := by
    calc
      Real.rpow 2 (((3 / 2 : ℝ) * (s : ℝ) ^ 2) * (e : ℝ))
          = Real.rpow 2 ((((2 * s - 4 : ℕ) : ℝ) * ((s * e : ℕ) : ℝ))) * C := by
            dsimp [C]
            rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
            congr 1
            have hs_cast : ((2 * s - 4 : ℕ) : ℝ) = 2 * (s : ℝ) - 4 := by
              rw [Nat.cast_sub (by omega : 4 ≤ 2 * s)]
              norm_num
            have hse_cast : ((s * e : ℕ) : ℝ) = (s : ℝ) * (e : ℝ) := by norm_num
            rw [hs_cast, hse_cast]
            ring
      _ < (N : ℝ) ^ (s * e) * C := by
            exact mul_lt_mul_of_pos_right hlower_pow hC_pos
  have hF_strict :
      ((F ^ e : ℕ) : ℝ) < (N : ℝ) ^ (s * e) * C :=
    lt_of_le_of_lt hFpow_real hpow_factor
  have harith :
      (n : ℝ) ^ s * C ≤ 1 := by
    simpa [C, e] using RandomHomomorphismFinalColorArithmetic ell s n hell hn
  have hnF_strict :
      (n : ℝ) ^ s * ((F ^ e : ℕ) : ℝ) < (N : ℝ) ^ (s * e) := by
    calc
      (n : ℝ) ^ s * ((F ^ e : ℕ) : ℝ)
          < (n : ℝ) ^ s * ((N : ℝ) ^ (s * e) * C) := by
            exact mul_lt_mul_of_pos_left hF_strict (pow_pos (by exact_mod_cast hn_pos_nat) s)
      _ = (N : ℝ) ^ (s * e) * ((n : ℝ) ^ s * C) := by ring
      _ ≤ (N : ℝ) ^ (s * e) * 1 := by
            exact mul_le_mul_of_nonneg_left harith (by positivity)
      _ = (N : ℝ) ^ (s * e) := by ring
  have hB_real_lt :
      ((Nat.choose n s * F ^ e * N ^ (e * (n - s)) : ℕ) : ℝ) <
        (N : ℝ) ^ (e * n) := by
    calc
      ((Nat.choose n s * F ^ e * N ^ (e * (n - s)) : ℕ) : ℝ)
          = ((Nat.choose n s : ℕ) : ℝ) * ((F ^ e : ℕ) : ℝ) *
              ((N ^ (e * (n - s)) : ℕ) : ℝ) := by norm_num
      _ ≤ (n : ℝ) ^ s * ((F ^ e : ℕ) : ℝ) *
              ((N ^ (e * (n - s)) : ℕ) : ℝ) := by
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right hchoose_real (by positivity))
              (by positivity)
      _ < (N : ℝ) ^ (s * e) * ((N ^ (e * (n - s)) : ℕ) : ℝ) := by
            have hNpow_pos_real : 0 < ((N ^ (e * (n - s)) : ℕ) : ℝ) := by
              exact_mod_cast (pow_pos hN_pos_nat (e * (n - s)))
            exact mul_lt_mul_of_pos_right hnF_strict hNpow_pos_real
      _ = (N : ℝ) ^ (e * n) := by
            have hcastpow : ((N ^ (e * (n - s)) : ℕ) : ℝ) =
                (N : ℝ) ^ (e * (n - s)) := by norm_num
            rw [hcastpow, ← pow_add]
            congr 1
            rw [Nat.mul_comm s e, ← Nat.mul_add, Nat.add_sub_of_le hsn]
  have htotal_card :
      Fintype.card Ω = N ^ (e * n) := by
    dsimp [Ω, N, e]
    rw [Fintype.card_fun, Fintype.card_fin]
    rw [Fintype.card_fun, Fintype.card_fin]
    rw [← pow_mul]
    congr 1
    rw [Nat.mul_comm]
  have hbad_real :
      (Fintype.card {phi : Ω // Bad phi} : ℝ) <
        (Fintype.card Ω : ℝ) := by
    calc
      (Fintype.card {phi : Ω // Bad phi} : ℝ)
          ≤ ((Nat.choose n s * F ^ e * N ^ (e * (n - s)) : ℕ) : ℝ) := by
            exact_mod_cast hupper_nat
      _ < (N : ℝ) ^ (e * n) := hB_real_lt
      _ = (Fintype.card Ω : ℝ) := by
            rw [htotal_card]
            norm_num
  exact_mod_cast hbad_real

