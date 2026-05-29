import Tablet.LoopGraphNdLambda

-- [TABLET NODE: LoopGraphNdLambdaAdjacencyIndicatorSum]

universe u

open Classical in
theorem LoopGraphNdLambdaAdjacencyIndicatorSum {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) (B : Finset V) :
    (∑ v : V, LoopGraphAdjacencyAction G
      (fun b : V => if b ∈ B then (1 : ℝ) else 0) v) =
        (d : ℝ) * (B.card : ℝ) := by
-- BODY
  classical
  let iB : V → ℝ := fun b => if b ∈ B then (1 : ℝ) else 0
  have hsym : LoopGraphSymmetric G := hG.2.1
  have hdeg : ∀ v : V, LoopGraphDegree G v = d := hG.2.2.1
  have hsum_indicator :
      (∑ b : V, iB b) = (B.card : ℝ) := by
    dsimp [iB]
    rw [Finset.sum_boole (fun b : V => b ∈ B) Finset.univ]
    have hfilter :
        (Finset.univ.filter (fun b : V => b ∈ B)) = B := by
      ext b
      simp
    simp [hfilter]
  calc
    (∑ v : V, LoopGraphAdjacencyAction G iB v)
        = ∑ v : V, ∑ b : V, if G v b then iB b else 0 := by
          simp [LoopGraphAdjacencyAction]
    _ = ∑ b : V, ∑ v : V, if G v b then iB b else 0 := by
          rw [Finset.sum_comm]
    _ = ∑ b : V, ∑ v : V, if G b v then iB b else 0 := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          refine Finset.sum_congr rfl ?_
          intro v hv
          by_cases hvb : G v b
          · have hbv : G b v := hsym hvb
            simp [hvb, hbv]
          · have hnot : ¬ G b v := by
              intro hbv
              exact hvb (hsym hbv)
            simp [hvb, hnot]
    _ = ∑ b : V, (LoopGraphDegree G b : ℝ) * iB b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          have hboole :
              (∑ v : V, if G b v then (1 : ℝ) else 0) =
                (LoopGraphDegree G b : ℝ) := by
            rw [Finset.sum_boole (fun v : V => G b v) Finset.univ]
            simp [LoopGraphDegree]
          calc
            (∑ v : V, if G b v then iB b else 0)
                = iB b * (∑ v : V, if G b v then (1 : ℝ) else 0) := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl ?_
                  intro v hv
                  by_cases hgbv : G b v <;> simp [hgbv]
            _ = (LoopGraphDegree G b : ℝ) * iB b := by
                  rw [hboole]
                  ring
    _ = ∑ b : V, (d : ℝ) * iB b := by
          refine Finset.sum_congr rfl ?_
          intro b hb
          rw [hdeg b]
    _ = (d : ℝ) * (B.card : ℝ) := by
          rw [← hsum_indicator]
          rw [Finset.mul_sum]
