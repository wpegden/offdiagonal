import Tablet.HsFreePair
import Tablet.ForwardIndependentTupleCount
import Tablet.ProductDigraph
import Tablet.ProductDigraphShrinkingSequenceBound
import Tablet.ProductDigraphTransitiveFree
import Tablet.ProductDigraphVertex
import Tablet.ProductDigraphVertexCard
import Tablet.ProductDigraphTupleHasShrinkingSequence
import Tablet.LoopGraphDegree
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: ProductDigraphForwardIndependentBound]

universe u

theorem ProductDigraphForwardIndependentBound {V : Type u} [Fintype V]
    (F G : LoopGraph V) (s n dF dG : ℕ) (lambdaF lambdaG eta w : ℝ)
    (hs : 3 ≤ s) (hn : 3 ≤ n) (hdF : 0 < dF) (hdG : 0 < dG)
    (hF : LoopGraphNdLambda F n dF lambdaF)
    (hG : LoopGraphNdLambda G n dG lambdaG)
    (hFG : HsFreePair F G s)
    (heta : eta =
      max (lambdaG ^ 2 / (dG : ℝ) ^ 2)
        (lambdaF * lambdaG / ((dF : ℝ) * (dG : ℝ))))
    (hw : w = 4 * (n : ℝ) * Real.log (n : ℝ) / (dG : ℝ))
    (heta_nonneg : 0 ≤ eta) (heta_le_one : eta ≤ 1) :
    ∃ (W : Type u) (_ : Fintype W), ∃ D : Digraph W,
      TransitiveTournamentFree D s ∧
        Fintype.card W = dF * n ∧
          ∀ k : ℕ, w ≤ (k : ℝ) →
            ((ForwardIndependentTupleCount D k : ℕ) : ℝ) ≤
              (16 : ℝ) ^ k * Real.rpow eta ((k : ℝ) - w) *
                ((dF * n : ℕ) : ℝ) ^ k := by
-- BODY
  classical
  letI : Fintype (ProductDigraphVertex F) := Fintype.ofFinite _
  refine ⟨ProductDigraphVertex F, inferInstance, ProductDigraph F G, ?_, ?_, ?_⟩
  · exact ProductDigraphTransitiveFree F G s hFG
  · exact ProductDigraphVertexCard F n dF lambdaF hF
  · intro k hk
    let survivingSet :
        {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v} → Fin k → Finset V :=
      fun v i =>
        Finset.univ.filter
          (fun b : V => ∀ j : Fin k, j < i → ¬ G (v.val j).val.1 b)
    let shrinkingSequence :
        {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v} → Fin k → Bool :=
      fun v i =>
        decide
          (((dG : ℝ) * (((survivingSet v i).card : ℕ) : ℝ)) /
              (2 * (n : ℝ)) <
            ((LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V)
              (survivingSet v i) : ℕ) : ℝ))
    have hshrinkingSequence :
        ∀ v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v},
          ProductDigraphTupleHasShrinkingSequence F G n dG v.val (shrinkingSequence v) := by
      intro v
      unfold ProductDigraphTupleHasShrinkingSequence
      refine ⟨v.property, ?_⟩
      intro i
      simp [shrinkingSequence, survivingSet]
    have hsecondCoordinate_mem_surviving :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k),
          (v.val i).val.2 ∈ survivingSet v i := by
      intro v i
      simp [survivingSet]
      intro j hji
      exact (by
        simpa [ProductDigraph] using v.property j i hji)
    have hsurvivingSet_nonempty :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k),
          (survivingSet v i).Nonempty := by
      intro v i
      exact ⟨(v.val i).val.2, hsecondCoordinate_mem_surviving v i⟩
    have hsurvivingSet_card_pos :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k),
          0 < (survivingSet v i).card := by
      intro v i
      exact Finset.card_pos.mpr (hsurvivingSet_nonempty v i)
    have hsingleton_edge_count_le_surviving :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k),
          LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V) (survivingSet v i) ≤
            (survivingSet v i).card := by
      intro v i
      unfold LoopGraphEdgeCountBetween
      calc
        (({(v.val i).val.1} ×ˢ survivingSet v i).filter
              (fun p : V × V => G p.1 p.2)).card
            ≤ ({(v.val i).val.1} ×ˢ survivingSet v i).card :=
              Finset.card_filter_le _ _
        _ = (survivingSet v i).card := by simp
    have hsingleton_edge_count_eq_filter :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k),
          LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V) (survivingSet v i) =
            ((survivingSet v i).filter (fun b : V => G (v.val i).val.1 b)).card := by
      intro v i
      unfold LoopGraphEdgeCountBetween
      refine Finset.card_bij (fun p _hp => p.2) ?_ ?_ ?_
      · intro p hp
        have hp_filter := Finset.mem_filter.mp hp
        have hp_prod := Finset.mem_product.mp hp_filter.1
        have hp1 : p.1 = (v.val i).val.1 := by simpa using hp_prod.1
        have hp2 : p.2 ∈ survivingSet v i := hp_prod.2
        exact Finset.mem_filter.mpr ⟨hp2, by simpa [hp1] using hp_filter.2⟩
      · intro p hp q hq hpq
        have hp_filter := Finset.mem_filter.mp hp
        have hq_filter := Finset.mem_filter.mp hq
        have hp_prod := Finset.mem_product.mp hp_filter.1
        have hq_prod := Finset.mem_product.mp hq_filter.1
        apply Prod.ext
        · have hp1 : p.1 = (v.val i).val.1 := by simpa using hp_prod.1
          have hq1 : q.1 = (v.val i).val.1 := by simpa using hq_prod.1
          rw [hp1, hq1]
        · exact hpq
      · intro b hb
        have hb' := Finset.mem_filter.mp hb
        refine ⟨((v.val i).val.1, b), ?_, rfl⟩
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_product.mpr ⟨by simp, hb'.1⟩, hb'.2⟩
    have htrue_large_neighborhood :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k),
          shrinkingSequence v i = true →
            ((dG : ℝ) * (((survivingSet v i).card : ℕ) : ℝ)) /
                (2 * (n : ℝ)) <
              ((LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V)
                (survivingSet v i) : ℕ) : ℝ) := by
      intro v i hbit
      exact ((hshrinkingSequence v).2 i).mp hbit
    have htrue_fraction_lt_card :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k),
          shrinkingSequence v i = true →
            ((dG : ℝ) * (((survivingSet v i).card : ℕ) : ℝ)) /
                (2 * (n : ℝ)) <
              ((survivingSet v i).card : ℝ) := by
      intro v i hbit
      have hlarge := htrue_large_neighborhood v i hbit
      have hedge_le :
          ((LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V)
              (survivingSet v i) : ℕ) : ℝ) ≤
            ((survivingSet v i).card : ℝ) := by
        exact_mod_cast hsingleton_edge_count_le_surviving v i
      exact lt_of_lt_of_le hlarge hedge_le
    have hsurvivingSet_succ :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k)
          (hi : i.val + 1 < k),
          survivingSet v ⟨i.val + 1, hi⟩ =
            (survivingSet v i).filter (fun b : V => ¬ G (v.val i).val.1 b) := by
      intro v i hi
      ext b
      simp only [survivingSet, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hb
        constructor
        · intro j hji
          exact hb j (lt_trans hji (by exact Nat.lt_succ_self i.val))
        · exact hb i (by exact Nat.lt_succ_self i.val)
      · intro hb
        rcases hb with ⟨hb_prev, hb_i⟩
        intro j hj
        by_cases hji : j < i
        · exact hb_prev j hji
        · have hge : i ≤ j := le_of_not_gt hji
          have hge_val : i.val ≤ j.val := hge
          have hj_val : j.val < i.val + 1 := hj
          have hval_eq : j.val = i.val := by
            omega
          have hji_eq : j = i := Fin.ext hval_eq
          simpa [hji_eq] using hb_i
    have htrue_shrink_recurrence :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k)
          (hi : i.val + 1 < k),
          shrinkingSequence v i = true →
            (((survivingSet v ⟨i.val + 1, hi⟩).card : ℕ) : ℝ) <
              (1 - (dG : ℝ) / (2 * (n : ℝ))) *
                (((survivingSet v i).card : ℕ) : ℝ) := by
      intro v i hi hbit
      have hnext_card :
          (survivingSet v ⟨i.val + 1, hi⟩).card =
            (survivingSet v i).card -
              LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V)
                (survivingSet v i) := by
        have hsucc_card := congrArg Finset.card (hsurvivingSet_succ v i hi)
        have hpartition :=
          Finset.card_filter_add_card_filter_not
            (s := survivingSet v i) (p := fun b : V => G (v.val i).val.1 b)
        rw [hsucc_card, hsingleton_edge_count_eq_filter v i]
        omega
      have hnext_card_real :
          (((survivingSet v ⟨i.val + 1, hi⟩).card : ℕ) : ℝ) =
            ((survivingSet v i).card : ℝ) -
              ((LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V)
                (survivingSet v i) : ℕ) : ℝ) := by
        rw [hnext_card]
        rw [Nat.cast_sub (hsingleton_edge_count_le_surviving v i)]
      have hlarge := htrue_large_neighborhood v i hbit
      calc
        (((survivingSet v ⟨i.val + 1, hi⟩).card : ℕ) : ℝ)
            = ((survivingSet v i).card : ℝ) -
                ((LoopGraphEdgeCountBetween G ({(v.val i).val.1} : Finset V)
                  (survivingSet v i) : ℕ) : ℝ) := hnext_card_real
        _ < ((survivingSet v i).card : ℝ) -
              ((dG : ℝ) * (((survivingSet v i).card : ℕ) : ℝ)) /
                (2 * (n : ℝ)) := by linarith
        _ = (1 - (dG : ℝ) / (2 * (n : ℝ))) *
              (((survivingSet v i).card : ℕ) : ℝ) := by ring
    have hsurvivingSet_succ_card_le :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (i : Fin k)
          (hi : i.val + 1 < k),
          (survivingSet v ⟨i.val + 1, hi⟩).card ≤ (survivingSet v i).card := by
      intro v i hi
      rw [hsurvivingSet_succ v i hi]
      exact Finset.card_filter_le _ _
    have hdG_le_n : dG ≤ n := by
      have hVpos : 0 < Fintype.card V := by
        rw [hG.1]
        linarith
      rcases Fintype.card_pos_iff.mp hVpos with ⟨v0⟩
      have hdegree_le_card : LoopGraphDegree G v0 ≤ Fintype.card V := by
        simpa [LoopGraphDegree] using
          (Finset.card_filter_le (Finset.univ : Finset V) (fun w : V => G v0 w))
      calc
        dG = LoopGraphDegree G v0 := (hG.2.2.1 v0).symm
        _ ≤ Fintype.card V := hdegree_le_card
        _ = n := hG.1
    let shrinkFactor : ℝ := 1 - (dG : ℝ) / (2 * (n : ℝ))
    have hn_pos : 0 < n := by linarith
    have hnR_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos
    have hdGR_pos : 0 < (dG : ℝ) := by exact_mod_cast hdG
    have hhalf_degree_le_one :
        (dG : ℝ) / (2 * (n : ℝ)) ≤ 1 := by
      have hdGnR : (dG : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdG_le_n
      have hnR_nonneg : 0 ≤ (n : ℝ) := le_of_lt hnR_pos
      have hden_pos : 0 < 2 * (n : ℝ) := by positivity
      rw [div_le_iff₀ hden_pos]
      nlinarith
    have hhalf_degree_pos :
        0 < (dG : ℝ) / (2 * (n : ℝ)) := by positivity
    have hshrinkFactor_nonneg : 0 ≤ shrinkFactor := by
      dsimp [shrinkFactor]
      linarith
    have hshrinkFactor_lt_one : shrinkFactor < 1 := by
      dsimp [shrinkFactor]
      linarith
    have hshrinkFactor_le_exp :
        shrinkFactor ≤ Real.exp (-((dG : ℝ) / (2 * (n : ℝ)))) := by
      dsimp [shrinkFactor]
      simpa using Real.one_sub_le_exp_neg ((dG : ℝ) / (2 * (n : ℝ)))
    have hw_nonneg : 0 ≤ w := by
      have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ n by linarith))
      rw [hw]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hnR_pos)) hlog_nonneg)
        (le_of_lt hdGR_pos)
    have hweight_card_le :
        ∀ v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v},
          BinarySequenceWeight (shrinkingSequence v) ≤ k := by
      intro v
      simpa [BinarySequenceWeight] using
        (Finset.card_filter_le (Finset.univ : Finset (Fin k))
          (fun i : Fin k => shrinkingSequence v i = true))
    have hweight_card_le_real :
        ∀ v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v},
          ((BinarySequenceWeight (shrinkingSequence v) : ℕ) : ℝ) ≤ (k : ℝ) := by
      intro v
      exact_mod_cast hweight_card_le v
    have hshrinkingWeightBound :
        ∀ v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v},
          ((BinarySequenceWeight (shrinkingSequence v) : ℕ) : ℝ) ≤ w := by
      intro v
      by_cases hk_zero : k = 0
      · subst k
        simpa [BinarySequenceWeight] using hw_nonneg
      · sorry
    sorry
