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
  let a : ℝ := (8 : ℝ) * eta
  let b : ℝ := (((dF * n : ℕ) : ℝ))
  have heta_nonneg : 0 ≤ eta := by
    have hleft :
        lambdaG ^ 2 / (dG : ℝ) ^ 2 ≤ eta := by
      rw [heta]
      exact le_max_left _ _
    have hfirst_nonneg :
        0 ≤ lambdaG ^ 2 / (dG : ℝ) ^ 2 := by
      exact div_nonneg (sq_nonneg _) (sq_nonneg _)
    exact le_trans hfirst_nonneg hleft
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    exact mul_nonneg (by norm_num) heta_nonneg
  have hb_nonneg : 0 ≤ b := by
    dsimp [b]
    positivity
  change
    ((ProductDigraphFixedSequenceTupleCount F G n dG t z : ℕ) : ℝ) ≤
      a ^ (t - BinarySequenceWeight z) * b ^ t
  induction t with
  | zero =>
      simp [ProductDigraphFixedSequenceTupleCount, ProductDigraphTupleHasShrinkingSequence,
        BinarySequenceWeight]
      refine Fintype.card_le_one_iff_subsingleton.mpr ?_
      exact ⟨fun x y => by
        apply Subtype.ext
        funext i
        exact Fin.elim0 i⟩
  | succ m ih =>
      let zp : Fin m → Bool := fun i : Fin m => z i.castSucc
      have hih :
          ((ProductDigraphFixedSequenceTupleCount F G n dG m zp : ℕ) : ℝ) ≤
            a ^ (m - BinarySequenceWeight zp) * b ^ m := ih zp
      have hweight_le : BinarySequenceWeight zp ≤ m := by
        simpa [BinarySequenceWeight] using
          (Finset.card_filter_le (Finset.univ : Finset (Fin m))
            (fun i : Fin m => zp i = true))
      by_cases hlast : z (Fin.last m) = true
      · have hstep :
            ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) z : ℕ) : ℝ) ≤
              ((ProductDigraphFixedSequenceTupleCount F G n dG m zp : ℕ) : ℝ) * b := by
          simpa [b, zp] using hOneStepTrue z hlast
        have hcombined :
            ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) z : ℕ) : ℝ) ≤
              (a ^ (m - BinarySequenceWeight zp) * b ^ m) * b := by
          exact le_trans hstep (mul_le_mul_of_nonneg_right hih hb_nonneg)
        have hweight : BinarySequenceWeight z = BinarySequenceWeight zp + 1 := by
          simpa [zp] using hWeightLastTrue z hlast
        have hexp :
            (m + 1) - BinarySequenceWeight z = m - BinarySequenceWeight zp := by
          rw [hweight]
          omega
        calc
          ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) z : ℕ) : ℝ)
              ≤ (a ^ (m - BinarySequenceWeight zp) * b ^ m) * b := hcombined
          _ = a ^ ((m + 1) - BinarySequenceWeight z) * b ^ (m + 1) := by
              rw [hexp, pow_succ]
              ring
      · have hlast_false : z (Fin.last m) = false := by
          cases hbit : z (Fin.last m) <;> simp [hbit] at hlast ⊢
        have hab_nonneg : 0 ≤ a * b := mul_nonneg ha_nonneg hb_nonneg
        have hstep :
            ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) z : ℕ) : ℝ) ≤
              ((ProductDigraphFixedSequenceTupleCount F G n dG m zp : ℕ) : ℝ) * (a * b) := by
          simpa [a, b, zp, mul_assoc] using hOneStepFalse z hlast_false
        have hcombined :
            ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) z : ℕ) : ℝ) ≤
              (a ^ (m - BinarySequenceWeight zp) * b ^ m) * (a * b) := by
          exact le_trans hstep (mul_le_mul_of_nonneg_right hih hab_nonneg)
        have hweight : BinarySequenceWeight z = BinarySequenceWeight zp := by
          simpa [zp] using hWeightLastFalse z hlast_false
        have hexp :
            (m + 1) - BinarySequenceWeight z =
              (m - BinarySequenceWeight zp) + 1 := by
          rw [hweight]
          omega
        calc
          ((ProductDigraphFixedSequenceTupleCount F G n dG (m + 1) z : ℕ) : ℝ)
              ≤ (a ^ (m - BinarySequenceWeight zp) * b ^ m) * (a * b) := hcombined
          _ = a ^ ((m + 1) - BinarySequenceWeight z) * b ^ (m + 1) := by
              rw [hexp, pow_succ, pow_succ]
              ring
