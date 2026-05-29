import Tablet.LoopGraphEdgeCountBetween
import Tablet.LoopGraphNdLambda
import Tablet.LoopGraphNdLambdaAdjacencyOne
import Tablet.LoopGraphEdgeCountBetweenAdjacencyIndicator
import Tablet.FinsetCenteredIndicatorSumZero
import Tablet.FinsetCenteredIndicatorNormSqLeCard

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
  by_cases hn_card : ((Fintype.card V : ℕ) : ℝ) = 0
  ·
    -- The remaining proof needs the empty-vertex case and then the spectral
    -- operator norm bound on the zero-sum subspace.
    sorry
  ·
    have hCenteredA :
        (∑ v : V, ((if v ∈ A then (1 : ℝ) else 0) -
          (A.card : ℝ) / (Fintype.card V : ℝ))) = 0 :=
      FinsetCenteredIndicatorSumZero A hn_card
    have hCenteredB :
        (∑ v : V, ((if v ∈ B then (1 : ℝ) else 0) -
          (B.card : ℝ) / (Fintype.card V : ℝ))) = 0 :=
      FinsetCenteredIndicatorSumZero B hn_card
    have hNormA :
        (∑ v : V, (((if v ∈ A then (1 : ℝ) else 0) -
          (A.card : ℝ) / (Fintype.card V : ℝ)) ^ 2)) ≤ (A.card : ℝ) :=
      FinsetCenteredIndicatorNormSqLeCard A hn_card
    have hNormB :
        (∑ v : V, (((if v ∈ B then (1 : ℝ) else 0) -
          (B.card : ℝ) / (Fintype.card V : ℝ)) ^ 2)) ≤ (B.card : ℝ) :=
      FinsetCenteredIndicatorNormSqLeCard B hn_card
    sorry
