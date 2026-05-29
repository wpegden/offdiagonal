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
  sorry
