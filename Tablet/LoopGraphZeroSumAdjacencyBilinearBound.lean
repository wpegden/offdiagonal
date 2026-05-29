import Tablet.LoopGraphNdLambda
import Tablet.LoopGraphAdjacencyActionSelfAdjoint
import Tablet.LoopGraphNdLambdaAdjacencyActionZeroSum
import Tablet.LoopGraphAdjacencyEuclideanInner
import Tablet.LoopGraphZeroSumAdjacencyEuclideanOperator
import Tablet.LoopGraphZeroSumEuclideanEigenvalueBound
import Tablet.LoopGraphAdjacencyEuclideanOperatorSymmetric

-- [TABLET NODE: LoopGraphZeroSumAdjacencyBilinearBound]

universe u

theorem LoopGraphZeroSumAdjacencyBilinearBound {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda)
    (f g : V → ℝ)
    (hf : (∑ v : V, f v) = 0)
    (hg : (∑ v : V, g v) = 0) :
    |(∑ v : V, f v * LoopGraphAdjacencyAction G g v)| ≤
      lambda * (Real.sqrt (∑ v : V, f v ^ 2) *
        Real.sqrt (∑ v : V, g v ^ 2)) := by
-- BODY
  have hSelfAdjoint :
      (∑ v : V, f v * LoopGraphAdjacencyAction G g v) =
        ∑ v : V, LoopGraphAdjacencyAction G f v * g v :=
    LoopGraphAdjacencyActionSelfAdjoint G hG.2.1 f g
  have hf_invariant :
      (∑ v : V, LoopGraphAdjacencyAction G f v) = 0 :=
    LoopGraphNdLambdaAdjacencyActionZeroSum G n d lambda hG f hf
  have hg_invariant :
      (∑ v : V, LoopGraphAdjacencyAction G g v) = 0 :=
    LoopGraphNdLambdaAdjacencyActionZeroSum G n d lambda hG g hg
  have hEuclideanInner :
      inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ V)
        (LoopGraphAdjacencyEuclideanOperator G (WithLp.toLp 2 g)) =
        ∑ v : V, f v * LoopGraphAdjacencyAction G g v :=
    LoopGraphAdjacencyEuclideanInner G f g
  let W := LoopGraphEuclideanZeroSumSubmodule V
  have hf_mem : (WithLp.toLp 2 f : EuclideanSpace ℝ V) ∈ W := by
    simpa [W, LoopGraphEuclideanZeroSumSubmodule] using hf
  have hg_mem : (WithLp.toLp 2 g : EuclideanSpace ℝ V) ∈ W := by
    simpa [W, LoopGraphEuclideanZeroSumSubmodule] using hg
  let fW : W := ⟨(WithLp.toLp 2 f : EuclideanSpace ℝ V), hf_mem⟩
  let gW : W := ⟨(WithLp.toLp 2 g : EuclideanSpace ℝ V), hg_mem⟩
  let TW := LoopGraphZeroSumAdjacencyEuclideanOperator G n d lambda hG
  have hTWg_coe :
      ((TW gW : W) : EuclideanSpace ℝ V) =
        LoopGraphAdjacencyEuclideanOperator G (WithLp.toLp 2 g) := rfl
  have hEuclideanEigenvalueBound :
      ∀ (mu : ℝ) (x : W), x ≠ 0 →
        LoopGraphAdjacencyEuclideanOperator G (x : EuclideanSpace ℝ V) =
          mu • (x : EuclideanSpace ℝ V) → |mu| ≤ lambda := by
    intro mu x hx hEigen
    exact LoopGraphZeroSumEuclideanEigenvalueBound G n d lambda mu hG x hx hEigen
  have hFullEuclideanSymmetric :
      LinearMap.IsSymmetric (LoopGraphAdjacencyEuclideanOperator G) :=
    LoopGraphAdjacencyEuclideanOperatorSymmetric G hG.2.1
  have hTW_symmetric : LinearMap.IsSymmetric TW := by
    intro x y
    change inner ℝ (LoopGraphAdjacencyEuclideanOperator G (x : EuclideanSpace ℝ V))
        (y : EuclideanSpace ℝ V) =
      inner ℝ (x : EuclideanSpace ℝ V)
        (LoopGraphAdjacencyEuclideanOperator G (y : EuclideanSpace ℝ V))
    exact hFullEuclideanSymmetric (x : EuclideanSpace ℝ V) (y : EuclideanSpace ℝ V)
  let B := hTW_symmetric.eigenvectorBasis (n := Module.finrank ℝ W) rfl
  have hEigenBasisApply :
      ∀ i : Fin (Module.finrank ℝ W),
        TW (B i) =
          (hTW_symmetric.eigenvalues rfl i : ℝ) • B i := by
    intro i
    exact hTW_symmetric.apply_eigenvectorBasis rfl i
  have hBasisNonzero :
      ∀ i : Fin (Module.finrank ℝ W), B i ≠ 0 := by
    intro i hzero
    have hnorm : ‖B i‖ = (1 : ℝ) := by
      simp
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hEigenBasisEigenvalueBound :
      ∀ i : Fin (Module.finrank ℝ W),
        |(hTW_symmetric.eigenvalues rfl i : ℝ)| ≤ lambda := by
    intro i
    have hEigRestricted := hEigenBasisApply i
    have hEigEuclidean := congrArg
      (fun z : W => (z : EuclideanSpace ℝ V)) hEigRestricted
    exact hEuclideanEigenvalueBound (hTW_symmetric.eigenvalues rfl i) (B i)
      (hBasisNonzero i) (by
        simp [TW, LoopGraphZeroSumAdjacencyEuclideanOperator] at hEigEuclidean
        exact hEigEuclidean)
  have hLambda : 0 ≤ lambda := hG.2.2.2.2
  have hOperatorNormBound :
      ∀ x : W, ‖TW x‖ ≤ lambda * ‖x‖ := by
    intro x
    have hCoordSq :
        ∀ i : Fin (Module.finrank ℝ W),
          ((B.repr (TW x)).ofLp i) ^ 2 ≤
            lambda ^ 2 * ((B.repr x).ofLp i) ^ 2 := by
      intro i
      have hcoord :
          ((B.repr (TW x)).ofLp i) =
            (hTW_symmetric.eigenvalues rfl i : ℝ) * ((B.repr x).ofLp i) := by
        simpa [B] using hTW_symmetric.eigenvectorBasis_apply_self_apply rfl x i
      have hmu := hEigenBasisEigenvalueBound i
      have hmu_sq :
          (hTW_symmetric.eigenvalues rfl i : ℝ) ^ 2 ≤ lambda ^ 2 := by
        have hnonneg : 0 ≤ |(hTW_symmetric.eigenvalues rfl i : ℝ)| :=
          abs_nonneg _
        have hsquare :
            |(hTW_symmetric.eigenvalues rfl i : ℝ)| ^ 2 =
              (hTW_symmetric.eigenvalues rfl i : ℝ) ^ 2 := by
          exact sq_abs _
        nlinarith
      have hxcoord_nonneg : 0 ≤ ((B.repr x).ofLp i) ^ 2 := sq_nonneg _
      calc
        ((B.repr (TW x)).ofLp i) ^ 2 =
            ((hTW_symmetric.eigenvalues rfl i : ℝ) * (B.repr x).ofLp i) ^ 2 := by
              rw [hcoord]
        _ = ((hTW_symmetric.eigenvalues rfl i : ℝ) ^ 2) *
            ((B.repr x).ofLp i) ^ 2 := by
              ring
        _ ≤ lambda ^ 2 * ((B.repr x).ofLp i) ^ 2 := by
              exact mul_le_mul_of_nonneg_right hmu_sq hxcoord_nonneg
    have hCoordSumSq :
        (∑ i : Fin (Module.finrank ℝ W), ((B.repr (TW x)).ofLp i) ^ 2) ≤
          lambda ^ 2 * ∑ i : Fin (Module.finrank ℝ W), ((B.repr x).ofLp i) ^ 2 := by
      calc
        (∑ i : Fin (Module.finrank ℝ W), ((B.repr (TW x)).ofLp i) ^ 2) ≤
            ∑ i : Fin (Module.finrank ℝ W),
              lambda ^ 2 * ((B.repr x).ofLp i) ^ 2 := by
              exact Finset.sum_le_sum (fun i _ => hCoordSq i)
        _ = lambda ^ 2 *
            ∑ i : Fin (Module.finrank ℝ W), ((B.repr x).ofLp i) ^ 2 := by
              rw [Finset.mul_sum]
    have hNormSqRepr :
        ‖B.repr (TW x)‖ ^ 2 ≤ lambda ^ 2 * ‖B.repr x‖ ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq]
      exact hCoordSumSq
    have hNormSq :
        ‖TW x‖ ^ 2 ≤ lambda ^ 2 * ‖x‖ ^ 2 := by
      simpa using hNormSqRepr
    have hNormSqTarget :
        ‖TW x‖ ^ 2 ≤ (lambda * ‖x‖) ^ 2 := by
      nlinarith
    have habs : |‖TW x‖| ≤ |lambda * ‖x‖| := (sq_le_sq).mp hNormSqTarget
    have hleft_abs : |‖TW x‖| = ‖TW x‖ :=
      abs_of_nonneg (norm_nonneg (TW x))
    have hright_abs : |lambda * ‖x‖| = lambda * ‖x‖ :=
      abs_of_nonneg (mul_nonneg hLambda (norm_nonneg x))
    rw [hleft_abs, hright_abs] at habs
    exact habs
  have hEuclideanBilinearBound :
      |inner ℝ fW (TW gW)| ≤ lambda * (‖fW‖ * ‖gW‖) := by
    have hCauchy : |inner ℝ fW (TW gW)| ≤ ‖fW‖ * ‖TW gW‖ :=
      abs_real_inner_le_norm fW (TW gW)
    have hNormG : ‖TW gW‖ ≤ lambda * ‖gW‖ :=
      hOperatorNormBound gW
    calc
      |inner ℝ fW (TW gW)| ≤ ‖fW‖ * ‖TW gW‖ := hCauchy
      _ ≤ ‖fW‖ * (lambda * ‖gW‖) := by
        exact mul_le_mul_of_nonneg_left hNormG (norm_nonneg fW)
      _ = lambda * (‖fW‖ * ‖gW‖) := by
        ring
  have hInnerSubmodule :
      inner ℝ fW (TW gW) =
        inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ V)
          (LoopGraphAdjacencyEuclideanOperator G (WithLp.toLp 2 g)) := by
    change inner ℝ (fW : EuclideanSpace ℝ V)
        ((TW gW : W) : EuclideanSpace ℝ V) =
      inner ℝ (WithLp.toLp 2 f : EuclideanSpace ℝ V)
        (LoopGraphAdjacencyEuclideanOperator G (WithLp.toLp 2 g))
    rw [hTWg_coe]
  have hFiniteSumBilinear :
      |(∑ v : V, f v * LoopGraphAdjacencyAction G g v)| ≤
        lambda * (‖fW‖ * ‖gW‖) := by
    rw [← hEuclideanInner, ← hInnerSubmodule]
    exact hEuclideanBilinearBound
  have hfW_norm :
      ‖fW‖ = Real.sqrt (∑ v : V, f v ^ 2) := by
    have hfEuclideanNorm :
        ‖(WithLp.toLp 2 f : EuclideanSpace ℝ V)‖ =
          Real.sqrt (∑ v : V, f v ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      simp [Real.norm_eq_abs, sq_abs]
    simpa [fW] using hfEuclideanNorm
  have hgW_norm :
      ‖gW‖ = Real.sqrt (∑ v : V, g v ^ 2) := by
    have hgEuclideanNorm :
        ‖(WithLp.toLp 2 g : EuclideanSpace ℝ V)‖ =
          Real.sqrt (∑ v : V, g v ^ 2) := by
      rw [EuclideanSpace.norm_eq]
      congr 1
      apply Finset.sum_congr rfl
      intro v hv
      simp [Real.norm_eq_abs, sq_abs]
    simpa [gW] using hgEuclideanNorm
  calc
    |(∑ v : V, f v * LoopGraphAdjacencyAction G g v)| ≤
        lambda * (‖fW‖ * ‖gW‖) := hFiniteSumBilinear
    _ = lambda * (Real.sqrt (∑ v : V, f v ^ 2) *
        Real.sqrt (∑ v : V, g v ^ 2)) := by
          rw [hfW_norm, hgW_norm]
