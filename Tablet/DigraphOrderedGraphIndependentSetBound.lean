import Tablet.DigraphOrderedGraph
import Tablet.DigraphOrderedGraphIndependentSetFactorialBound
import Tablet.DigraphOrderedGraphIndependentSetToForwardTuple
import Tablet.ForwardIndependentTupleCount
import Tablet.SimpleGraphIndependentSetCount
import Tablet.TupleIncreasingPermutationFiberCount

-- [TABLET NODE: DigraphOrderedGraphIndependentSetBound]

universe u

theorem DigraphOrderedGraphIndependentSetBound {W : Type u} [Fintype W]
    (D : Digraph W) (k : ℕ) (hk : 1 ≤ k) :
    ∃ r : W → ℕ,
      ((SimpleGraphIndependentSetCount (DigraphOrderedGraph D r) k : ℕ) : ℝ) ≤
        (Real.exp 1 / (k : ℝ)) ^ k *
          ((ForwardIndependentTupleCount D k : ℕ) : ℝ) := by
-- BODY
  classical
  rcases DigraphOrderedGraphIndependentSetFactorialBound (D := D) (k := k) with
    ⟨r, hfact_count⟩
  refine ⟨r, ?_⟩
  let I : ℕ := SimpleGraphIndependentSetCount (DigraphOrderedGraph D r) k
  let F : ℕ := ForwardIndependentTupleCount D k
  have hmul_real : ((Nat.factorial k : ℝ) * (I : ℝ)) ≤ (F : ℝ) := by
    have hcast : (((Nat.factorial k * I : ℕ) : ℝ) ≤ (F : ℝ)) := by
      exact_mod_cast hfact_count
    simpa [I, F, Nat.cast_mul] using hcast
  have hfac_pos : (0 : ℝ) < (Nat.factorial k : ℝ) := by
    exact_mod_cast Nat.factorial_pos k
  have hI_le_div : (I : ℝ) ≤ (F : ℝ) / (Nat.factorial k : ℝ) := by
    rw [le_div_iff₀ hfac_pos]
    simpa [mul_comm] using hmul_real
  have hI_le_inv : (I : ℝ) ≤ (1 / (Nat.factorial k : ℝ)) * (F : ℝ) := by
    simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hI_le_div
  have hkpos_nat : 0 < k := Nat.lt_of_lt_of_le Nat.zero_lt_one hk
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast hkpos_nat
  have h_exp :=
    Real.pow_div_factorial_le_exp (k : ℝ) (show 0 ≤ (k : ℝ) by positivity) k
  have hdiv : ((k : ℝ) ^ k / (Nat.factorial k : ℝ)) / (k : ℝ) ^ k ≤
      Real.exp (k : ℝ) / (k : ℝ) ^ k := by
    exact div_le_div_of_nonneg_right h_exp (by positivity)
  have hleft : ((k : ℝ) ^ k / (Nat.factorial k : ℝ)) / (k : ℝ) ^ k =
      (1 : ℝ) / (Nat.factorial k : ℝ) := by
    field_simp [pow_ne_zero _ hkpos.ne']
  have hright : Real.exp (k : ℝ) / (k : ℝ) ^ k =
      (Real.exp 1 / (k : ℝ)) ^ k := by
    rw [div_pow]
    congr 1
    rw [← Real.exp_nat_mul]
    norm_num
  have hfac_bound :
      (1 : ℝ) / (Nat.factorial k : ℝ) ≤ (Real.exp 1 / (k : ℝ)) ^ k := by
    simpa [hleft, hright] using hdiv
  have hmul_bound :
      (1 / (Nat.factorial k : ℝ)) * (F : ℝ) ≤
        (Real.exp 1 / (k : ℝ)) ^ k * (F : ℝ) := by
    exact mul_le_mul_of_nonneg_right hfac_bound (by positivity)
  calc
    ((SimpleGraphIndependentSetCount (DigraphOrderedGraph D r) k : ℕ) : ℝ)
        = (I : ℝ) := by simp [I]
    _ ≤ (1 / (Nat.factorial k : ℝ)) * (F : ℝ) := hI_le_inv
    _ ≤ (Real.exp 1 / (k : ℝ)) ^ k * (F : ℝ) := hmul_bound
    _ = (Real.exp 1 / (k : ℝ)) ^ k *
        ((ForwardIndependentTupleCount D k : ℕ) : ℝ) := by simp [F]
