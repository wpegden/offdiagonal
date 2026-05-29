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
  sorry
