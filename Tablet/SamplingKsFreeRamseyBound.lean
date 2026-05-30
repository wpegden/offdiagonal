import Tablet.RamseyNumber
import Tablet.SimpleGraphIndependentSetCount

-- [TABLET NODE: SamplingKsFreeRamseyBound]

universe u

theorem SamplingKsFreeRamseyBound {V : Type u} [Fintype V]
    (G : SimpleGraph V) (s k : ℕ) (p : ℝ)
    (hKs : ¬ ∃ S : Finset V, G.IsNClique s S)
    (hk : 1 ≤ k)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hcount : Real.rpow p (k : ℝ) *
      ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) ≤ 1) :
    p * (Fintype.card V : ℝ) - 1 < (RamseyNumber s k : ℝ) := by
-- BODY
  classical
  have hfiniteDeletion :
      ∀ {W : Type u} [Fintype W] (F : SimpleGraph W),
        (¬ ∃ S : Finset W, F.IsNClique s S) →
          ∃ (Hverts : Type u) (_ : Fintype Hverts), ∃ H : SimpleGraph Hverts,
            (¬ ∃ S : Finset Hverts, H.IsNClique s S) ∧
              (¬ ∃ I : Finset Hverts, Hᶜ.IsNClique k I) ∧
                Fintype.card W - SimpleGraphIndependentSetCount F k ≤
                  Fintype.card Hverts := by
    intro W hW F hKsF
    let independentSets := {S : Finset W // Fᶜ.IsNClique k S}
    have hindependent_nonempty :
        ∀ S : independentSets, S.val.Nonempty := by
      intro S
      exact Finset.card_pos.mp (by
        rw [S.property.card_eq]
        exact Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
    let chosenVertex : independentSets → W :=
      fun S => Classical.choose (hindependent_nonempty S)
    have hchosen_mem :
        ∀ S : independentSets, chosenVertex S ∈ S.val := by
      intro S
      exact Classical.choose_spec (hindependent_nonempty S)
    let deleted : Finset W :=
      (Finset.univ : Finset independentSets).image chosenVertex
    have hdeleted_card_le_count :
        deleted.card ≤ SimpleGraphIndependentSetCount F k := by
      calc
        deleted.card ≤ (Finset.univ : Finset independentSets).card := by
          dsimp [deleted]
          exact Finset.card_image_le
        _ = Fintype.card independentSets := by
          simp
        _ = SimpleGraphIndependentSetCount F k := by
          simp [SimpleGraphIndependentSetCount, independentSets]
    let Hverts : Type u := {x : W // x ∉ deleted}
    letI : Fintype Hverts := inferInstance
    let H : SimpleGraph Hverts := F.induce {x : W | x ∉ deleted}
    have hH_KsFree :
        ¬ ∃ S : Finset Hverts, H.IsNClique s S := by
      rintro ⟨S, hS⟩
      apply hKsF
      let emb : Hverts ↪ W := ⟨Subtype.val, Subtype.val_injective⟩
      refine ⟨S.map emb, ?_⟩
      refine ⟨?_, ?_⟩
      · intro x hx y hy hxy
        rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
        rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
        have hxy' : x' ≠ y' := by
          intro hxy_eq
          exact hxy (by simp [emb, hxy_eq])
        have hadj := hS.isClique hx' hy' hxy'
        simpa [H, emb, SimpleGraph.induce_adj] using hadj
      · simpa [emb] using (Finset.card_map (f := emb) (s := S)).trans hS.card_eq
    have hH_no_independent :
        ¬ ∃ I : Finset Hverts, Hᶜ.IsNClique k I := by
      rintro ⟨I, hI⟩
      let emb : Hverts ↪ W := ⟨Subtype.val, Subtype.val_injective⟩
      have hI_in_F : Fᶜ.IsNClique k (I.map emb) := by
        refine ⟨?_, ?_⟩
        · intro x hx y hy hxy
          rcases Finset.mem_map.mp hx with ⟨x', hx', rfl⟩
          rcases Finset.mem_map.mp hy with ⟨y', hy', rfl⟩
          have hxy' : x' ≠ y' := by
            intro hxy_eq
            exact hxy (by simp [emb, hxy_eq])
          have hadj := hI.isClique hx' hy' hxy'
          change Fᶜ.Adj x'.val y'.val
          refine ⟨?_, ?_⟩
          · intro hval
            exact hxy' (Subtype.ext hval)
          · exact hadj.2
        · simpa [emb] using (Finset.card_map (f := emb) (s := I)).trans hI.card_eq
      let J : independentSets := ⟨I.map emb, hI_in_F⟩
      have hchosen_in_image : chosenVertex J ∈ I.map emb := hchosen_mem J
      have hchosen_deleted : chosenVertex J ∈ deleted := by
        dsimp [deleted]
        exact Finset.mem_image.mpr ⟨J, by simp, rfl⟩
      rcases Finset.mem_map.mp hchosen_in_image with ⟨x, _hxI, hxeq⟩
      exact x.property (by simpa [← hxeq] using hchosen_deleted)
    have hH_card :
        Fintype.card Hverts = Fintype.card W - deleted.card := by
      dsimp [Hverts]
      rw [Fintype.card_subtype_compl (fun x : W => x ∈ deleted)]
      simp
    have hH_card_ge :
        Fintype.card W - SimpleGraphIndependentSetCount F k ≤
          Fintype.card Hverts := by
      rw [hH_card]
      exact Nat.sub_le_sub_left hdeleted_card_le_count (Fintype.card W)
    exact ⟨Hverts, inferInstance, H, hH_KsFree, hH_no_independent, hH_card_ge⟩
  let bernoulliWeight : Finset V → ℝ :=
    fun U => p ^ U.card * (1 - p) ^ (Fintype.card V - U.card)
  have hbernoulliWeight_nonneg :
      ∀ U : Finset V, 0 ≤ bernoulliWeight U := by
    intro U
    dsimp [bernoulliWeight]
    exact mul_nonneg (pow_nonneg hp0 _)
      (pow_nonneg (by linarith : 0 ≤ (1 : ℝ) - p) _)
  have hbernoulliWeight_total :
      (∑ U : Finset V, bernoulliWeight U) = 1 := by
    dsimp [bernoulliWeight]
    calc
      (∑ U : Finset V,
          p ^ U.card * (1 - p) ^ (Fintype.card V - U.card))
          = (p + (1 - p)) ^ Fintype.card V := by
            exact Fintype.sum_pow_mul_eq_add_pow V p (1 - p)
      _ = 1 := by
            ring_nf
  have hbernoulliExpectedVertexCount :
      (∑ U : Finset V, bernoulliWeight U * (U.card : ℝ)) =
        p * (Fintype.card V : ℝ) := by
    have hcard_indicator :
        ∀ U : Finset V,
          (U.card : ℝ) = ∑ v : V, if v ∈ U then (1 : ℝ) else 0 := by
      intro U
      calc
        (U.card : ℝ) = ∑ v ∈ U, (1 : ℝ) := by simp
        _ = ∑ v : V, if v ∈ U then (1 : ℝ) else 0 := by
          rw [← Finset.sum_filter]
          simp
    have hvertex_mass :
        ∀ v : V, (∑ U : Finset V, if v ∈ U then bernoulliWeight U else 0) = p := by
      intro v
      let rest : Finset V := (Finset.univ : Finset V).erase v
      have hrest_card : rest.card = Fintype.card V - 1 := by
        dsimp [rest]
        rw [Finset.card_erase_of_mem]
        · simp
        · simp
      have hcontains_to_filter :
          (∑ U : Finset V, if v ∈ U then bernoulliWeight U else 0) =
            ∑ U ∈ (Finset.univ : Finset (Finset V)).filter (fun U => v ∈ U),
              bernoulliWeight U := by
        rw [← Finset.sum_filter]
      have hfilter_to_rest :
          (∑ U ∈ (Finset.univ : Finset (Finset V)).filter (fun U => v ∈ U),
              bernoulliWeight U) =
            ∑ T ∈ rest.powerset, bernoulliWeight (insert v T) := by
        symm
        refine Finset.sum_bij
          (fun T _ => insert v T)
          ?hi ?hinj ?hsurj ?hval
        · intro T hT
          exact Finset.mem_filter.mpr ⟨by simp, by simp⟩
        · intro T₁ hT₁ T₂ hT₂ heq
          have hvT₁ : v ∉ T₁ := by
            have hsub := Finset.mem_powerset.mp hT₁
            intro hv
            have : v ∈ rest := hsub hv
            exact Finset.notMem_erase v (Finset.univ : Finset V) this
          have hvT₂ : v ∉ T₂ := by
            have hsub := Finset.mem_powerset.mp hT₂
            intro hv
            have : v ∈ rest := hsub hv
            exact Finset.notMem_erase v (Finset.univ : Finset V) this
          calc
            T₁ = (insert v T₁).erase v := (Finset.erase_insert hvT₁).symm
            _ = (insert v T₂).erase v := by
              simpa using congrArg (fun U : Finset V => U.erase v) heq
            _ = T₂ := Finset.erase_insert hvT₂
        · intro U hU
          have hvU : v ∈ U := (Finset.mem_filter.mp hU).2
          refine ⟨U.erase v, ?_, ?_⟩
          · exact Finset.mem_powerset.mpr (by
              intro x hx
              dsimp [rest]
              exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, by simp⟩)
          · exact Finset.insert_erase hvU
        · intro T hT
          rfl
      calc
        (∑ U : Finset V, if v ∈ U then bernoulliWeight U else 0)
            = ∑ T ∈ rest.powerset, bernoulliWeight (insert v T) := by
              rw [hcontains_to_filter, hfilter_to_rest]
        _ = ∑ T ∈ rest.powerset,
              p * (p ^ T.card * (1 - p) ^ (rest.card - T.card)) := by
              refine Finset.sum_congr rfl ?_
              intro T hT
              dsimp [bernoulliWeight]
              have hv_not_mem : v ∉ T := by
                have hsub := Finset.mem_powerset.mp hT
                intro hv
                have : v ∈ rest := hsub hv
                exact Finset.notMem_erase v (Finset.univ : Finset V) this
              have hcard_insert :
                  (insert v T).card = T.card + 1 := by
                rw [Finset.card_insert_of_notMem hv_not_mem]
              have hdiff :
                  Fintype.card V - (insert v T).card =
                    rest.card - T.card := by
                rw [hcard_insert, hrest_card]
                omega
              rw [hdiff, hcard_insert]
              rw [pow_succ]
              ring
        _ = p * ∑ T ∈ rest.powerset,
              p ^ T.card * (1 - p) ^ (rest.card - T.card) := by
              rw [Finset.mul_sum]
        _ = p * (p + (1 - p)) ^ rest.card := by
              rw [Finset.sum_pow_mul_eq_add_pow]
        _ = p * 1 := by
              ring_nf
        _ = p := by ring
    calc
      (∑ U : Finset V, bernoulliWeight U * (U.card : ℝ))
          = ∑ U : Finset V, bernoulliWeight U *
              (∑ v : V, if v ∈ U then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro U hU
            rw [hcard_indicator U]
      _ = ∑ U : Finset V, ∑ v : V,
              bernoulliWeight U * (if v ∈ U then (1 : ℝ) else 0) := by
            refine Finset.sum_congr rfl ?_
            intro U hU
            rw [Finset.mul_sum]
      _ = ∑ v : V, ∑ U : Finset V,
              bernoulliWeight U * (if v ∈ U then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ v : V, p := by
            refine Finset.sum_congr rfl ?_
            intro v hv
            calc
              (∑ U : Finset V, bernoulliWeight U *
                  (if v ∈ U then (1 : ℝ) else 0))
                  = ∑ U : Finset V, if v ∈ U then bernoulliWeight U else 0 := by
                    refine Finset.sum_congr rfl ?_
                    intro U hU
                    by_cases hmem : v ∈ U <;> simp [hmem]
              _ = p := hvertex_mass v
      _ = p * (Fintype.card V : ℝ) := by
            simp [mul_comm]
  have hfixedIndependentSetMass_pow :
      ∀ I : {S : Finset V // Gᶜ.IsNClique k S},
        (∑ U : Finset V, if I.val ⊆ U then bernoulliWeight U else 0) = p ^ k := by
    intro I
    let base : Finset V := I.val
    let rest : Finset V := (Finset.univ : Finset V) \ base
    have hbase_card : base.card = k := by
      dsimp [base]
      exact I.property.card_eq
    have hrest_card : rest.card = Fintype.card V - base.card := by
      dsimp [rest]
      rw [Finset.card_sdiff_of_subset (by simp)]
      simp
    have hcontains_to_filter :
        (∑ U : Finset V, if base ⊆ U then bernoulliWeight U else 0) =
          ∑ U ∈ (Finset.univ : Finset (Finset V)).filter (fun U => base ⊆ U),
            bernoulliWeight U := by
      rw [← Finset.sum_filter]
    have hfilter_to_rest :
        (∑ U ∈ (Finset.univ : Finset (Finset V)).filter (fun U => base ⊆ U),
            bernoulliWeight U) =
          ∑ T ∈ rest.powerset, bernoulliWeight (base ∪ T) := by
      symm
      refine Finset.sum_bij
        (fun T _ => base ∪ T)
        ?hIndHi ?hIndInj ?hIndSurj ?hIndVal
      · intro T hT
        exact Finset.mem_filter.mpr ⟨by simp, by simp⟩
      · intro T₁ hT₁ T₂ hT₂ heq
        have hdisj₁ : Disjoint base T₁ := by
          refine Finset.disjoint_left.mpr ?_
          intro x hxbase hxT
          have hsub := Finset.mem_powerset.mp hT₁
          have hxrest : x ∈ rest := hsub hxT
          exact (Finset.mem_sdiff.mp hxrest).2 hxbase
        have hdisj₂ : Disjoint base T₂ := by
          refine Finset.disjoint_left.mpr ?_
          intro x hxbase hxT
          have hsub := Finset.mem_powerset.mp hT₂
          have hxrest : x ∈ rest := hsub hxT
          exact (Finset.mem_sdiff.mp hxrest).2 hxbase
        calc
          T₁ = (base ∪ T₁) \ base := (Finset.union_sdiff_cancel_left hdisj₁).symm
          _ = (base ∪ T₂) \ base := by
            simpa using congrArg (fun U : Finset V => U \ base) heq
          _ = T₂ := Finset.union_sdiff_cancel_left hdisj₂
      · intro U hU
        have hbaseU : base ⊆ U := (Finset.mem_filter.mp hU).2
        refine ⟨U \ base, ?_, ?_⟩
        · exact Finset.mem_powerset.mpr (by
            intro x hx
            dsimp [rest]
            exact Finset.mem_sdiff.mpr ⟨by simp, (Finset.mem_sdiff.mp hx).2⟩)
        · simpa [Finset.union_comm] using Finset.sdiff_union_of_subset hbaseU
      · intro T hT
        rfl
    calc
      (∑ U : Finset V, if I.val ⊆ U then bernoulliWeight U else 0)
          = ∑ U : Finset V, if base ⊆ U then bernoulliWeight U else 0 := by
            dsimp [base]
      _ = ∑ T ∈ rest.powerset, bernoulliWeight (base ∪ T) := by
            rw [hcontains_to_filter, hfilter_to_rest]
      _ = ∑ T ∈ rest.powerset,
            p ^ k * (p ^ T.card * (1 - p) ^ (rest.card - T.card)) := by
            refine Finset.sum_congr rfl ?_
            intro T hT
            dsimp [bernoulliWeight]
            have hdisj : Disjoint base T := by
              refine Finset.disjoint_left.mpr ?_
              intro x hxbase hxT
              have hsub := Finset.mem_powerset.mp hT
              have hxrest : x ∈ rest := hsub hxT
              exact (Finset.mem_sdiff.mp hxrest).2 hxbase
            have hcard_union : (base ∪ T).card = base.card + T.card := by
              rw [Finset.card_union_of_disjoint hdisj]
            have hdiff :
                Fintype.card V - (base ∪ T).card = rest.card - T.card := by
              rw [hcard_union, hrest_card]
              omega
            rw [hdiff, hcard_union, hbase_card]
            rw [pow_add]
            ring
      _ = p ^ k * ∑ T ∈ rest.powerset,
            p ^ T.card * (1 - p) ^ (rest.card - T.card) := by
            rw [Finset.mul_sum]
      _ = p ^ k * (p + (1 - p)) ^ rest.card := by
            rw [Finset.sum_pow_mul_eq_add_pow]
      _ = p ^ k := by
            ring_nf
  have hfixedIndependentSetMass :
      ∀ I : {S : Finset V // Gᶜ.IsNClique k S},
        (∑ U : Finset V, if I.val ⊆ U then bernoulliWeight U else 0) =
          Real.rpow p (k : ℝ) := by
    intro I
    calc
      (∑ U : Finset V, if I.val ⊆ U then bernoulliWeight U else 0) =
          p ^ k := hfixedIndependentSetMass_pow I
      _ = Real.rpow p (k : ℝ) := by
            exact (Real.rpow_natCast p k).symm
  have hsumFixedIndependentSetMasses :
      (∑ I : {S : Finset V // Gᶜ.IsNClique k S},
          (∑ U : Finset V, if I.val ⊆ U then bernoulliWeight U else 0)) =
        Real.rpow p (k : ℝ) *
          ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) := by
    let independentSets := {S : Finset V // Gᶜ.IsNClique k S}
    have hcount_independentSets :
        ((Fintype.card independentSets : ℕ) : ℝ) =
          ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) := by
      simp [SimpleGraphIndependentSetCount, independentSets]
    calc
      (∑ I : {S : Finset V // Gᶜ.IsNClique k S},
          (∑ U : Finset V, if I.val ⊆ U then bernoulliWeight U else 0))
          = ∑ I : independentSets, Real.rpow p (k : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro I hI
            exact hfixedIndependentSetMass I
      _ = ((Fintype.card independentSets : ℕ) : ℝ) * Real.rpow p (k : ℝ) := by
            simp
      _ = Real.rpow p (k : ℝ) *
          ((SimpleGraphIndependentSetCount G k : ℕ) : ℝ) := by
            rw [hcount_independentSets]
            ring
  sorry
