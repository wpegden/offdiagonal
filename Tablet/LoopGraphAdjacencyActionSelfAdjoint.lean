import Tablet.LoopGraphAdjacencyAction
import Tablet.LoopGraphSymmetric

-- [TABLET NODE: LoopGraphAdjacencyActionSelfAdjoint]

universe u

theorem LoopGraphAdjacencyActionSelfAdjoint {V : Type u} [Fintype V]
    (G : LoopGraph V) (hGsym : LoopGraphSymmetric G) (f g : V → ℝ) :
    (∑ v : V, f v * LoopGraphAdjacencyAction G g v) =
      ∑ v : V, LoopGraphAdjacencyAction G f v * g v := by
-- BODY
  classical
  calc
    (∑ v : V, f v * LoopGraphAdjacencyAction G g v)
        = ∑ v : V, ∑ w : V, if G v w then f v * g w else 0 := by
          simp [LoopGraphAdjacencyAction, Finset.mul_sum]
    _ = ∑ w : V, ∑ v : V, if G v w then f v * g w else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ w : V, ∑ v : V, if G w v then f v * g w else 0 := by
          refine Finset.sum_congr rfl ?_
          intro w hw
          refine Finset.sum_congr rfl ?_
          intro v hv
          by_cases hvw : G v w
          · have hwv : G w v := hGsym hvw
            simp [hvw, hwv]
          · have hnot : ¬ G w v := by
              intro hwv
              exact hvw (hGsym hwv)
            simp [hvw, hnot]
    _ = ∑ w : V, g w * LoopGraphAdjacencyAction G f w := by
          refine Finset.sum_congr rfl ?_
          intro w hw
          calc
            (∑ v : V, if G w v then f v * g w else 0)
                = ∑ v : V, g w * (if G w v then f v else 0) := by
                  refine Finset.sum_congr rfl ?_
                  intro v hv
                  by_cases hwv : G w v <;> simp [hwv, mul_comm]
            _ = g w * (∑ v : V, if G w v then f v else 0) := by
                  rw [Finset.mul_sum]
            _ = g w * LoopGraphAdjacencyAction G f w := by
                  simp [LoopGraphAdjacencyAction]
    _ = ∑ w : V, LoopGraphAdjacencyAction G f w * g w := by
          refine Finset.sum_congr rfl ?_
          intro w hw
          ring
