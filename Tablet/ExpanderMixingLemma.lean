import Tablet.LoopGraphEdgeCountBetween
import Tablet.LoopGraphNdLambda
import Tablet.LoopGraphNdLambdaAdjacencyOne
import Tablet.LoopGraphEdgeCountBetweenAdjacencyIndicator
import Tablet.FinsetCenteredIndicatorSumZero
import Tablet.FinsetCenteredIndicatorNormSqLeCard
import Tablet.LoopGraphNdLambdaAdjacencyIndicatorSum
import Tablet.LoopGraphZeroSumAdjacencyBilinearBound

-- [TABLET NODE: ExpanderMixingLemma]

universe u

theorem ExpanderMixingLemma {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) (A B : Finset V) :
    |((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) -
      ((d : ℝ) / (n : ℝ)) * (A.card : ℝ) * (B.card : ℝ)| ≤
        lambda * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
-- BODY
  classical
  have hAdjOne :
      ∀ v : V, LoopGraphAdjacencyAction G (fun _ : V => (1 : ℝ)) v = (d : ℝ) := by
    intro v
    exact LoopGraphNdLambdaAdjacencyOne G n d lambda hG v
  have hEdgeIndicator :
      ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) =
        ∑ a ∈ A, LoopGraphAdjacencyAction G
          (fun b : V => if b ∈ B then (1 : ℝ) else 0) a :=
    LoopGraphEdgeCountBetweenAdjacencyIndicator G A B
  have hLambdaNonneg : 0 ≤ lambda := hG.2.2.2.2
  by_cases hn_card : ((Fintype.card V : ℕ) : ℝ) = 0
  ·
    have hn_card_nat : Fintype.card V = 0 := by
      exact_mod_cast hn_card
    haveI : IsEmpty V := Fintype.card_eq_zero_iff.mp hn_card_nat
    have hAempty : A = ∅ := by
      ext v
      exact isEmptyElim v
    have hBempty : B = ∅ := by
      ext v
      exact isEmptyElim v
    simp [hAempty, hBempty, LoopGraphEdgeCountBetween]
  ·
    let iA : V → ℝ := fun v => if v ∈ A then (1 : ℝ) else 0
    let iB : V → ℝ := fun v => if v ∈ B then (1 : ℝ) else 0
    let f : V → ℝ := fun v => iA v - (A.card : ℝ) / (Fintype.card V : ℝ)
    let g : V → ℝ := fun v => iB v - (B.card : ℝ) / (Fintype.card V : ℝ)
    have hn_eq : (n : ℝ) = (Fintype.card V : ℝ) := by
      rw [← hG.1]
    have hCenteredA : (∑ v : V, f v) = 0 := by
      dsimp [f, iA]
      exact FinsetCenteredIndicatorSumZero A hn_card
    have hCenteredB : (∑ v : V, g v) = 0 := by
      dsimp [g, iB]
      exact FinsetCenteredIndicatorSumZero B hn_card
    have hNormA :
        (∑ v : V, f v ^ 2) ≤ (A.card : ℝ) := by
      dsimp [f, iA]
      exact FinsetCenteredIndicatorNormSqLeCard A hn_card
    have hNormB :
        (∑ v : V, g v ^ 2) ≤ (B.card : ℝ) := by
      dsimp [g, iB]
      exact FinsetCenteredIndicatorNormSqLeCard B hn_card
    have hEdgeUniv :
        ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) =
          ∑ v : V, iA v * LoopGraphAdjacencyAction G iB v := by
      calc
        ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ)
            = ∑ a ∈ A, LoopGraphAdjacencyAction G
              (fun b : V => if b ∈ B then (1 : ℝ) else 0) a := hEdgeIndicator
        _ = ∑ v : V, if v ∈ A then
              LoopGraphAdjacencyAction G (fun b : V => if b ∈ B then (1 : ℝ) else 0) v
            else 0 := by
              rw [← Finset.sum_filter]
              simp
        _ = ∑ v : V, iA v * LoopGraphAdjacencyAction G iB v := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              dsimp [iA, iB]
              by_cases hvA : v ∈ A <;> simp [hvA]
    have hSumAdjB :
        (∑ v : V, LoopGraphAdjacencyAction G iB v) = (d : ℝ) * (B.card : ℝ) := by
      dsimp [iB]
      exact LoopGraphNdLambdaAdjacencyIndicatorSum G n d lambda hG B
    have hAg : ∀ v : V,
        LoopGraphAdjacencyAction G g v =
          LoopGraphAdjacencyAction G iB v -
            ((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ) := by
      intro v
      calc
        LoopGraphAdjacencyAction G g v
            = LoopGraphAdjacencyAction G
                (fun w : V => iB w - ((B.card : ℝ) / (Fintype.card V : ℝ))) v := by
              rfl
        _ = LoopGraphAdjacencyAction G iB v -
              ((B.card : ℝ) / (Fintype.card V : ℝ)) *
                LoopGraphAdjacencyAction G (fun _ : V => (1 : ℝ)) v := by
              simp only [LoopGraphAdjacencyAction]
              calc
                (∑ w : V, if G v w then iB w - ↑B.card / ↑(Fintype.card V) else 0)
                    = ∑ w : V, ((if G v w then iB w else 0) -
                        (↑B.card / ↑(Fintype.card V)) *
                          (if G v w then (1 : ℝ) else 0)) := by
                      refine Finset.sum_congr rfl ?_
                      intro w hw
                      by_cases hgvw : G v w <;> simp [hgvw]
                _ = (∑ w : V, if G v w then iB w else 0) -
                      (↑B.card / ↑(Fintype.card V)) *
                        (∑ w : V, if G v w then (1 : ℝ) else 0) := by
                      rw [Finset.sum_sub_distrib, Finset.mul_sum]
        _ = LoopGraphAdjacencyAction G iB v -
              ((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ) := by
              rw [hAdjOne v]
    have hInnerEq :
        (∑ v : V, f v * LoopGraphAdjacencyAction G g v) =
          ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) -
            ((d : ℝ) / (n : ℝ)) * (A.card : ℝ) * (B.card : ℝ) := by
      calc
        (∑ v : V, f v * LoopGraphAdjacencyAction G g v)
            = ∑ v : V, f v * (LoopGraphAdjacencyAction G iB v -
                ((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ)) := by
              refine Finset.sum_congr rfl ?_
              intro v hv
              rw [hAg v]
        _ = ∑ v : V, f v * LoopGraphAdjacencyAction G iB v := by
              calc
                (∑ v : V, f v * (LoopGraphAdjacencyAction G iB v -
                    ((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ)))
                    = (∑ v : V, f v * LoopGraphAdjacencyAction G iB v) -
                        (((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ)) *
                          (∑ v : V, f v) := by
                          calc
                            (∑ v : V, f v * (LoopGraphAdjacencyAction G iB v -
                                ((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ)))
                                = ∑ v : V, (f v * LoopGraphAdjacencyAction G iB v -
                                    (((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ)) *
                                      f v) := by
                                  refine Finset.sum_congr rfl ?_
                                  intro v hv
                                  ring
                            _ = (∑ v : V, f v * LoopGraphAdjacencyAction G iB v) -
                                  ∑ v : V, (((B.card : ℝ) / (Fintype.card V : ℝ)) *
                                    (d : ℝ)) * f v := by
                                  rw [Finset.sum_sub_distrib]
                            _ = (∑ v : V, f v * LoopGraphAdjacencyAction G iB v) -
                                  (((B.card : ℝ) / (Fintype.card V : ℝ)) * (d : ℝ)) *
                                    (∑ v : V, f v) := by
                                  rw [Finset.mul_sum]
                _ = ∑ v : V, f v * LoopGraphAdjacencyAction G iB v := by
                    rw [hCenteredA]
                    ring
        _ = (∑ v : V, iA v * LoopGraphAdjacencyAction G iB v) -
              ((A.card : ℝ) / (Fintype.card V : ℝ)) *
                (∑ v : V, LoopGraphAdjacencyAction G iB v) := by
              dsimp [f]
              calc
                (∑ v : V, (iA v - ↑A.card / ↑(Fintype.card V)) *
                    LoopGraphAdjacencyAction G iB v)
                    = ∑ v : V, (iA v * LoopGraphAdjacencyAction G iB v -
                        (↑A.card / ↑(Fintype.card V)) *
                          LoopGraphAdjacencyAction G iB v) := by
                      refine Finset.sum_congr rfl ?_
                      intro v hv
                      ring
                _ = (∑ v : V, iA v * LoopGraphAdjacencyAction G iB v) -
                      ∑ v : V, (↑A.card / ↑(Fintype.card V)) *
                        LoopGraphAdjacencyAction G iB v := by
                      rw [Finset.sum_sub_distrib]
                _ = (∑ v : V, iA v * LoopGraphAdjacencyAction G iB v) -
                      (↑A.card / ↑(Fintype.card V)) *
                        (∑ v : V, LoopGraphAdjacencyAction G iB v) := by
                      rw [Finset.mul_sum]
        _ = ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) -
              ((A.card : ℝ) / (Fintype.card V : ℝ)) * ((d : ℝ) * (B.card : ℝ)) := by
              rw [← hEdgeUniv, hSumAdjB]
        _ = ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) -
              ((d : ℝ) / (n : ℝ)) * (A.card : ℝ) * (B.card : ℝ) := by
              rw [hn_eq]
              field_simp [hn_card]
    have hSpec :=
      LoopGraphZeroSumAdjacencyBilinearBound G n d lambda hG f g hCenteredA hCenteredB
    have hAbs :
        |((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ) -
            ((d : ℝ) / (n : ℝ)) * (A.card : ℝ) * (B.card : ℝ)| ≤
          lambda * (Real.sqrt (∑ v : V, f v ^ 2) *
            Real.sqrt (∑ v : V, g v ^ 2)) := by
      rw [← hInnerEq]
      exact hSpec
    have hsqrtA :
        Real.sqrt (∑ v : V, f v ^ 2) ≤ Real.sqrt (A.card : ℝ) :=
      Real.sqrt_le_sqrt hNormA
    have hsqrtB :
        Real.sqrt (∑ v : V, g v ^ 2) ≤ Real.sqrt (B.card : ℝ) :=
      Real.sqrt_le_sqrt hNormB
    have hprod :
        Real.sqrt (∑ v : V, f v ^ 2) * Real.sqrt (∑ v : V, g v ^ 2) ≤
          Real.sqrt (A.card : ℝ) * Real.sqrt (B.card : ℝ) := by
      exact mul_le_mul hsqrtA hsqrtB (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hprod' :
        lambda * (Real.sqrt (∑ v : V, f v ^ 2) * Real.sqrt (∑ v : V, g v ^ 2)) ≤
          lambda * Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) := by
      have hsqrt_mul :
          Real.sqrt ((A.card : ℝ) * (B.card : ℝ)) =
            Real.sqrt (A.card : ℝ) * Real.sqrt (B.card : ℝ) := by
        rw [Real.sqrt_mul]
        positivity
      rw [hsqrt_mul]
      exact mul_le_mul_of_nonneg_left hprod hLambdaNonneg
    exact le_trans hAbs hprod'
