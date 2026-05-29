import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Finset.Range
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
    have hsurvivingSet_zero_card :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (hkpos : 0 < k),
          (survivingSet v ⟨0, hkpos⟩).card = n := by
      intro v hkpos
      have hset :
          survivingSet v ⟨0, hkpos⟩ = (Finset.univ : Finset V) := by
        ext b
        simp only [survivingSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro _h
          trivial
        · intro _h j hj
          have hjval : j.val < 0 := hj
          omega
      rw [hset]
      exact hG.1
    have hshrinkFactor_pow_le_exp :
        ∀ r : ℕ,
          shrinkFactor ^ r ≤
            Real.exp (-((r : ℝ) * ((dG : ℝ) / (2 * (n : ℝ))))) := by
      intro r
      calc
        shrinkFactor ^ r
            ≤ (Real.exp (-((dG : ℝ) / (2 * (n : ℝ))))) ^ r := by
              exact pow_le_pow_left₀ hshrinkFactor_nonneg hshrinkFactor_le_exp r
        _ = Real.exp ((r : ℝ) * (-((dG : ℝ) / (2 * (n : ℝ))))) := by
              rw [← Real.exp_nat_mul]
        _ = Real.exp (-((r : ℝ) * ((dG : ℝ) / (2 * (n : ℝ))))) := by
              ring_nf
    let truePrefixCount :
        {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v} → ℕ → ℕ :=
      fun v r =>
        ((Finset.range r).filter
          (fun a : ℕ => ∃ ha : a < k, shrinkingSequence v ⟨a, ha⟩ = true)).card
    have htruePrefixCount_succ_true :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (r : ℕ) (hr : r < k),
          shrinkingSequence v ⟨r, hr⟩ = true →
            truePrefixCount v (r + 1) = truePrefixCount v r + 1 := by
      intro v r hr hbit
      dsimp [truePrefixCount]
      rw [Finset.range_add_one, Finset.filter_insert]
      simp [hr, hbit]
    have htruePrefixCount_succ_false :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (r : ℕ) (hr : r < k),
          shrinkingSequence v ⟨r, hr⟩ = false →
            truePrefixCount v (r + 1) = truePrefixCount v r := by
      intro v r hr hbit
      dsimp [truePrefixCount]
      rw [Finset.range_add_one, Finset.filter_insert]
      simp [hr, hbit]
    have hprefixCardBound :
        ∀ (v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v}) (r : ℕ) (hr : r < k),
          (((survivingSet v ⟨r, hr⟩).card : ℕ) : ℝ) ≤
            (n : ℝ) * shrinkFactor ^ truePrefixCount v r := by
      intro v r
      induction r with
      | zero =>
          intro hr
          rw [hsurvivingSet_zero_card v hr]
          simp [truePrefixCount]
      | succ r ih =>
          intro hr_succ
          have hr : r < k := Nat.lt_trans (Nat.lt_succ_self r) hr_succ
          by_cases hbit : shrinkingSequence v ⟨r, hr⟩ = true
          · have hstep :
                (((survivingSet v ⟨r + 1, hr_succ⟩).card : ℕ) : ℝ) ≤
                  shrinkFactor * (((survivingSet v ⟨r, hr⟩).card : ℕ) : ℝ) := by
              exact le_of_lt (by
                simpa [shrinkFactor] using
                  htrue_shrink_recurrence v ⟨r, hr⟩ hr_succ hbit)
            have hih := ih hr
            calc
              (((survivingSet v ⟨r + 1, hr_succ⟩).card : ℕ) : ℝ)
                  ≤ shrinkFactor * (((survivingSet v ⟨r, hr⟩).card : ℕ) : ℝ) := hstep
              _ ≤ shrinkFactor * ((n : ℝ) * shrinkFactor ^ truePrefixCount v r) := by
                    exact mul_le_mul_of_nonneg_left hih hshrinkFactor_nonneg
              _ = (n : ℝ) * shrinkFactor ^ truePrefixCount v (r + 1) := by
                    rw [htruePrefixCount_succ_true v r hr hbit, pow_succ]
                    ring
          · have hbit_false : shrinkingSequence v ⟨r, hr⟩ = false := by
              cases h : shrinkingSequence v ⟨r, hr⟩ <;> simp [h] at hbit ⊢
            have hstep :
                (((survivingSet v ⟨r + 1, hr_succ⟩).card : ℕ) : ℝ) ≤
                  (((survivingSet v ⟨r, hr⟩).card : ℕ) : ℝ) := by
              exact_mod_cast hsurvivingSet_succ_card_le v ⟨r, hr⟩ hr_succ
            calc
              (((survivingSet v ⟨r + 1, hr_succ⟩).card : ℕ) : ℝ)
                  ≤ (((survivingSet v ⟨r, hr⟩).card : ℕ) : ℝ) := hstep
              _ ≤ (n : ℝ) * shrinkFactor ^ truePrefixCount v r := ih hr
              _ = (n : ℝ) * shrinkFactor ^ truePrefixCount v (r + 1) := by
                    rw [htruePrefixCount_succ_false v r hr hbit_false]
    have htruePrefixCount_all :
        ∀ v : {v : Fin k → ProductDigraphVertex F //
          ForwardIndependentTuple (ProductDigraph F G) v},
          truePrefixCount v k = BinarySequenceWeight (shrinkingSequence v) := by
      intro v
      unfold truePrefixCount BinarySequenceWeight
      refine Finset.card_bij
        (fun a ha => ⟨a, (Finset.mem_range.mp (Finset.mem_filter.mp ha).1)⟩) ?_ ?_ ?_
      · intro a ha
        have hfilter := Finset.mem_filter.mp ha
        rcases hfilter.2 with ⟨_ha_lt, hbit⟩
        exact Finset.mem_filter.mpr ⟨by simp, by simpa using hbit⟩
      · intro a ha b hb hab
        exact by
          simpa using congrArg Fin.val hab
      · intro i hi
        refine ⟨i.val, ?_, ?_⟩
        · have hbit := (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr i.isLt, ⟨i.isLt, hbit⟩⟩
        · rfl
    have hw_nonneg : 0 ≤ w := by
      have hlog_nonneg : 0 ≤ Real.log (n : ℝ) := by
        exact Real.log_nonneg (by exact_mod_cast (show (1 : ℕ) ≤ n by linarith))
      rw [hw]
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (le_of_lt hnR_pos)) hlog_nonneg)
        (le_of_lt hdGR_pos)
    have hlog_n_gt_half : (1 / 2 : ℝ) < Real.log (n : ℝ) := by
      have htwo_le_n : (2 : ℝ) ≤ (n : ℝ) := by
        exact_mod_cast (show (2 : ℕ) ≤ n by linarith)
      have hlog_two_le_log_n : Real.log (2 : ℝ) ≤ Real.log (n : ℝ) := by
        exact Real.log_le_log (by norm_num) htwo_le_n
      have hhalf_lt_log_two : (1 / 2 : ℝ) < Real.log (2 : ℝ) := by
        exact lt_trans (by norm_num : (1 / 2 : ℝ) < 0.6931471803) Real.log_two_gt_d9
      exact lt_of_lt_of_le hhalf_lt_log_two hlog_two_le_log_n
    have hpaperExponentialEstimate :
        (n : ℝ) *
            Real.exp (-((w - 1) * ((dG : ℝ) / (2 * (n : ℝ))))) < 1 := by
      have hhalf_degree_le_half :
          (dG : ℝ) / (2 * (n : ℝ)) ≤ 1 / 2 := by
        have hdGnR : (dG : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdG_le_n
        have hden_pos : 0 < 2 * (n : ℝ) := by positivity
        rw [div_le_iff₀ hden_pos]
        nlinarith
      have heq_lower :
          (w - 1) * ((dG : ℝ) / (2 * (n : ℝ))) =
            2 * Real.log (n : ℝ) - (dG : ℝ) / (2 * (n : ℝ)) := by
        rw [hw]
        field_simp [hdGR_pos.ne', hnR_pos.ne']
        ring
      have hlower :
          2 * Real.log (n : ℝ) - 1 / 2 ≤
            (w - 1) * ((dG : ℝ) / (2 * (n : ℝ))) := by
        rw [heq_lower]
        linarith [hhalf_degree_le_half]
      have hneg_le :
          -((w - 1) * ((dG : ℝ) / (2 * (n : ℝ)))) ≤
            -(2 * Real.log (n : ℝ) - 1 / 2) := by
        linarith
      have hexp_le :
          Real.exp (-((w - 1) * ((dG : ℝ) / (2 * (n : ℝ))))) ≤
            Real.exp (-(2 * Real.log (n : ℝ) - 1 / 2)) := by
        exact Real.exp_le_exp.mpr hneg_le
      have hmain_le :
          (n : ℝ) *
              Real.exp (-((w - 1) * ((dG : ℝ) / (2 * (n : ℝ))))) ≤
            (n : ℝ) * Real.exp (-(2 * Real.log (n : ℝ) - 1 / 2)) := by
        exact mul_le_mul_of_nonneg_left hexp_le (le_of_lt hnR_pos)
      have htarget :
          (n : ℝ) * Real.exp (-(2 * Real.log (n : ℝ) - 1 / 2)) < 1 := by
        calc
          (n : ℝ) * Real.exp (-(2 * Real.log (n : ℝ) - 1 / 2))
              = Real.exp (Real.log (n : ℝ)) *
                  Real.exp (-(2 * Real.log (n : ℝ) - 1 / 2)) := by
                    rw [Real.exp_log hnR_pos]
          _ = Real.exp (1 / 2 - Real.log (n : ℝ)) := by
                    rw [← Real.exp_add]
                    congr 1
                    ring
          _ < Real.exp 0 := by
                    exact Real.exp_lt_exp.mpr (by linarith)
          _ = 1 := by simp
      exact lt_of_le_of_lt hmain_le htarget
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
      · by_contra hnot
        have hgt : w < ((BinarySequenceWeight (shrinkingSequence v) : ℕ) : ℝ) :=
          lt_of_not_ge hnot
        let trueIndices : Finset (Fin k) :=
          Finset.univ.filter (fun i : Fin k => shrinkingSequence v i = true)
        have htrueIndices_card :
            trueIndices.card = BinarySequenceWeight (shrinkingSequence v) := by
          simp [trueIndices, BinarySequenceWeight]
        have hweight_pos : 0 < BinarySequenceWeight (shrinkingSequence v) := by
          by_contra hpos
          have hzero : BinarySequenceWeight (shrinkingSequence v) = 0 :=
            Nat.eq_zero_of_not_pos hpos
          have hcast_zero :
              ((BinarySequenceWeight (shrinkingSequence v) : ℕ) : ℝ) = 0 := by
            simp [hzero]
          linarith
        have htrueIndices_nonempty : trueIndices.Nonempty := by
          rw [← Finset.card_pos, htrueIndices_card]
          exact hweight_pos
        let lastTrue : Fin k := trueIndices.max' htrueIndices_nonempty
        have hlast_mem : lastTrue ∈ trueIndices :=
          Finset.max'_mem trueIndices htrueIndices_nonempty
        have hlast_true : shrinkingSequence v lastTrue = true :=
          (Finset.mem_filter.mp hlast_mem).2
        have hprefix_after_last :
            truePrefixCount v (lastTrue.val + 1) =
              BinarySequenceWeight (shrinkingSequence v) := by
          unfold truePrefixCount BinarySequenceWeight
          refine Finset.card_bij
            (fun a ha => ⟨a, (Finset.mem_filter.mp ha).2.choose⟩) ?_ ?_ ?_
          · intro a ha
            have hfilter := Finset.mem_filter.mp ha
            rcases hfilter.2 with ⟨ha_lt, hbit⟩
            exact Finset.mem_filter.mpr ⟨by simp, by simpa using hbit⟩
          · intro a ha b hb hab
            exact by
              simpa using congrArg Fin.val hab
          · intro i hi
            have hi_trueIndices : i ∈ trueIndices := by
              simpa [trueIndices] using hi
            have hle : i ≤ lastTrue := Finset.le_max' trueIndices i hi_trueIndices
            have hval_le : i.val ≤ lastTrue.val := hle
            have hbit := (Finset.mem_filter.mp hi).2
            refine ⟨i.val, ?_, ?_⟩
            · exact Finset.mem_filter.mpr
                ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hval_le), ⟨i.isLt, hbit⟩⟩
            · rfl
        have htotal_eq :
            BinarySequenceWeight (shrinkingSequence v) =
              truePrefixCount v lastTrue.val + 1 := by
          rw [← hprefix_after_last]
          exact htruePrefixCount_succ_true v lastTrue.val lastTrue.isLt hlast_true
        have hprefix_gt :
            w - 1 < (truePrefixCount v lastTrue.val : ℝ) := by
          have hgt' : w < (truePrefixCount v lastTrue.val : ℝ) + 1 := by
            simpa [htotal_eq, Nat.cast_add] using hgt
          linarith
        have hcard_bound :=
          hprefixCardBound v lastTrue.val lastTrue.isLt
        have hpow_exp :=
          hshrinkFactor_pow_le_exp (truePrefixCount v lastTrue.val)
        have hpow_bound :
            (n : ℝ) * shrinkFactor ^ truePrefixCount v lastTrue.val ≤
              (n : ℝ) *
                Real.exp (-((truePrefixCount v lastTrue.val : ℝ) *
                  ((dG : ℝ) / (2 * (n : ℝ))))) := by
          exact mul_le_mul_of_nonneg_left hpow_exp (le_of_lt hnR_pos)
        have hexp_arg_lt :
            -((truePrefixCount v lastTrue.val : ℝ) *
                ((dG : ℝ) / (2 * (n : ℝ)))) <
              -((w - 1) * ((dG : ℝ) / (2 * (n : ℝ)))) := by
          nlinarith [hprefix_gt, hhalf_degree_pos]
        have hexp_strict :
            Real.exp (-((truePrefixCount v lastTrue.val : ℝ) *
                ((dG : ℝ) / (2 * (n : ℝ))))) <
              Real.exp (-((w - 1) * ((dG : ℝ) / (2 * (n : ℝ))))) := by
          exact Real.exp_lt_exp.mpr hexp_arg_lt
        have hprefix_rhs_lt_one :
            (n : ℝ) * shrinkFactor ^ truePrefixCount v lastTrue.val < 1 := by
          calc
            (n : ℝ) * shrinkFactor ^ truePrefixCount v lastTrue.val
                ≤ (n : ℝ) *
                    Real.exp (-((truePrefixCount v lastTrue.val : ℝ) *
                      ((dG : ℝ) / (2 * (n : ℝ))))) := hpow_bound
            _ < (n : ℝ) *
                    Real.exp (-((w - 1) * ((dG : ℝ) / (2 * (n : ℝ))))) := by
                  exact mul_lt_mul_of_pos_left hexp_strict hnR_pos
            _ < 1 := hpaperExponentialEstimate
        have hcard_lt_one :
            (((survivingSet v lastTrue).card : ℕ) : ℝ) < 1 :=
          lt_of_le_of_lt hcard_bound hprefix_rhs_lt_one
        have hcard_ge_one :
            (1 : ℝ) ≤ (((survivingSet v lastTrue).card : ℕ) : ℝ) := by
          exact_mod_cast (Nat.succ_le_of_lt (hsurvivingSet_card_pos v lastTrue))
        exact (not_lt_of_ge hcard_ge_one) hcard_lt_one
    sorry
