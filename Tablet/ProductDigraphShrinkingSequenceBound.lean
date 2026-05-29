import Tablet.BinarySequenceWeight
import Tablet.BinarySequenceWeightSnoc
import Tablet.ProductDigraphFixedSequenceTupleCount
import Tablet.ProductDigraphFixedSequenceTupleCountLastVertexBound
import Tablet.ProductDigraphFixedSequenceTupleCountZeroBitBound
import Tablet.ProductDigraphSparseEdgeChoiceBound
import Tablet.ProductDigraphVertexCard
import Tablet.SparseNeighborhoodSetBound

-- [TABLET NODE: ProductDigraphShrinkingSequenceBound]

universe u

theorem ProductDigraphShrinkingSequenceBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (n dF dG t : ℕ) (lambdaF lambdaG eta : ℝ)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hn : 0 < n) (hdF : 0 < dF) (hdG : 0 < dG)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (z : Fin t → Bool) :
    ((ProductDigraphFixedSequenceTupleCount F G n dG t z : ℕ) : ℝ) ≤
      ((8 : ℝ) * eta) ^ (t - BinarySequenceWeight z) *
        ((dF * n : ℕ) : ℝ) ^ t := by
-- BODY
  classical
  letI : Fintype (ProductDigraphVertex F) := Fintype.ofFinite _
  have hSparseChoice :
      ∀ A B : Finset V,
        (∀ u : V, u ∈ A ↔
          ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ) ≤
            ((dG : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ))) →
        ((LoopGraphEdgeCountBetween F A B : ℕ) : ℝ) ≤
          ((8 : ℝ) * eta) * (((dF * n : ℕ) : ℝ)) := by
    intro A B hA
    exact ProductDigraphSparseEdgeChoiceBound F G n dF dG lambdaF lambdaG eta
      hF hG hn hdF hdG heta A B hA
  have hOneBitChoice :
      Fintype.card (ProductDigraphVertex F) = dF * n :=
    ProductDigraphVertexCard F n dF lambdaF hF
  have hWeightSnoc :
      ∀ {m : ℕ} (w : Fin (m + 1) → Bool),
        BinarySequenceWeight w =
          BinarySequenceWeight (fun i : Fin m => w i.castSucc) +
            (if w (Fin.last m) = true then 1 else 0) := by
    intro m w
    exact BinarySequenceWeightSnoc w
  have hWeightLastFalse :
      ∀ {m : ℕ} (w : Fin (m + 1) → Bool),
        w (Fin.last m) = false →
          BinarySequenceWeight w =
            BinarySequenceWeight (fun i : Fin m => w i.castSucc) := by
    intro m w hw
    simpa [hw] using (BinarySequenceWeightSnoc w)
  have hWeightLastTrue :
      ∀ {m : ℕ} (w : Fin (m + 1) → Bool),
        w (Fin.last m) = true →
          BinarySequenceWeight w =
            BinarySequenceWeight (fun i : Fin m => w i.castSucc) + 1 := by
    intro m w hw
    simpa [hw] using (BinarySequenceWeightSnoc w)
  have hOneStepLastVertex :
      ∀ {m : ℕ} (w : Fin (m + 1) → Bool),
        ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) w : ℕ) : ℝ) ≤
          ((ProductDigraphFixedSequenceTupleCount F G n dG m
            (fun i : Fin m => w i.castSucc) : ℕ) : ℝ) *
            (((dF * n : ℕ) : ℝ)) := by
    intro m w
    exact ProductDigraphFixedSequenceTupleCountLastVertexBound F G n dF dG m lambdaF hF w
  have hOneStepTrue :
      ∀ {m : ℕ} (w : Fin (m + 1) → Bool),
        w (Fin.last m) = true →
        ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) w : ℕ) : ℝ) ≤
          ((ProductDigraphFixedSequenceTupleCount F G n dG m
            (fun i : Fin m => w i.castSucc) : ℕ) : ℝ) *
            (((dF * n : ℕ) : ℝ)) := by
    intro m w _hw
    exact hOneStepLastVertex w
  have hOneStepFalse :
      ∀ {m : ℕ} (w : Fin (m + 1) → Bool),
        w (Fin.last m) = false →
        ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) w : ℕ) : ℝ) ≤
          ((ProductDigraphFixedSequenceTupleCount F G n dG m
            (fun i : Fin m => w i.castSucc) : ℕ) : ℝ) *
            (((8 : ℝ) * eta) * (((dF * n : ℕ) : ℝ))) := by
    intro m w hw
    exact ProductDigraphFixedSequenceTupleCountZeroBitBound F G n dF dG m
      lambdaF lambdaG eta hF hG hn hdF hdG heta w hw
  sorry
