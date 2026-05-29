import Mathlib.Logic.Equiv.Fintype
import Tablet.DigraphOrderedGraph
import Tablet.ForwardIndependentTupleCount
import Tablet.SimpleGraphIndependentSetCount
import Tablet.TupleIncreasingPermutationFiberCount

-- [TABLET NODE: DigraphOrderedGraphIndependentSetFactorialBound]

universe u

theorem DigraphOrderedGraphIndependentSetFactorialBound {W : Type u} [Fintype W]
    (D : Digraph W) (k : ℕ) :
    ∃ r : W → ℕ,
      Nat.factorial k *
          SimpleGraphIndependentSetCount (DigraphOrderedGraph D r) k ≤
        ForwardIndependentTupleCount D k := by
-- BODY
  classical
  let e : W ≃ Fin (Fintype.card W) := Fintype.equivFin W
  let baseRank : W → ℕ := fun w => (e w : ℕ)
  have hbase_inj : Function.Injective baseRank := by
    intro x y hxy
    apply e.injective
    exact Fin.ext hxy
  let rank : Equiv.Perm W → W → ℕ := fun τ w => baseRank (τ w)
  have hrank_inj : ∀ τ : Equiv.Perm W, Function.Injective (rank τ) := by
    intro τ x y hxy
    exact τ.injective (hbase_inj hxy)
  let I : Equiv.Perm W → Type u := fun τ =>
    {S : Finset W // (DigraphOrderedGraph D (rank τ))ᶜ.IsNClique k S}
  let SortedData (τ : Equiv.Perm W) (S : I τ) : Type u :=
    {v : Fin k → W //
      Function.Injective v ∧
        Set.range v = (↑(S : Finset W) : Set W) ∧
          StrictMono (fun i : Fin k => rank τ (v i)) ∧
            ForwardIndependentTuple D v}
  have sortedData_nonempty : ∀ (τ : Equiv.Perm W) (S : I τ), Nonempty (SortedData τ S) := by
    intro τ S
    have hcard : (S : Finset W).card = k := S.2.card_eq
    have hClique : (DigraphOrderedGraph D (rank τ))ᶜ.IsClique (↑(S : Finset W) : Set W) :=
      S.2.isClique
    let R : Finset ℕ := (S : Finset W).image (rank τ)
    have hrinj : Set.InjOn (rank τ) (↑(S : Finset W) : Set W) := by
      intro x _ y _ hxy
      exact hrank_inj τ hxy
    have hRcard : R.card = k := by
      simp [R, Finset.card_image_of_injOn hrinj, hcard]
    let rankS : Fin k → ℕ := R.orderEmbOfFin hRcard
    have hrank_mem : ∀ i : Fin k, rankS i ∈ R := by
      intro i
      dsimp [rankS]
      exact Finset.orderEmbOfFin_mem R hRcard i
    have hpre : ∀ i : Fin k, ∃ w ∈ (S : Finset W), rank τ w = rankS i := by
      intro i
      have hi : rankS i ∈ (S : Finset W).image (rank τ) := by
        simpa [R] using hrank_mem i
      simpa using (Finset.mem_image.mp hi)
    let v : Fin k → W := fun i => Classical.choose (hpre i)
    have hv_mem : ∀ i : Fin k, v i ∈ (S : Finset W) := by
      intro i
      exact (Classical.choose_spec (hpre i)).1
    have hv_rank : ∀ i : Fin k, rank τ (v i) = rankS i := by
      intro i
      exact (Classical.choose_spec (hpre i)).2
    have hv_inj : Function.Injective v := by
      intro i j hij
      apply (R.orderEmbOfFin hRcard).injective
      calc
        rankS i = rank τ (v i) := (hv_rank i).symm
        _ = rank τ (v j) := by rw [hij]
        _ = rankS j := hv_rank j
    have hv_range : Set.range v = (↑(S : Finset W) : Set W) := by
      apply Set.ext
      intro x
      constructor
      · intro hx
        rcases hx with ⟨i, rfl⟩
        exact hv_mem i
      · intro hxS
        have hrx_mem : rank τ x ∈ R := by
          exact Finset.mem_image.mpr ⟨x, hxS, rfl⟩
        have hrx_range : rank τ x ∈ Set.range (R.orderEmbOfFin hRcard) := by
          rw [Finset.range_orderEmbOfFin R hRcard]
          exact hrx_mem
        rcases hrx_range with ⟨i, hi⟩
        refine ⟨i, ?_⟩
        apply hrinj (hv_mem i) hxS
        calc
          rank τ (v i) = rankS i := hv_rank i
          _ = rank τ x := hi
    have hv_strict : StrictMono (fun i : Fin k => rank τ (v i)) := by
      intro i j hij
      have hlt : rankS i < rankS j :=
        (R.orderEmbOfFin hRcard).strictMono hij
      simpa [hv_rank] using hlt
    have hv_fwd : ForwardIndependentTuple D v := by
      intro i j hij hDij
      have hr_lt : rank τ (v i) < rank τ (v j) := hv_strict hij
      have hne : v i ≠ v j := by
        intro hv
        exact (ne_of_lt hij) (hv_inj hv)
      have hcomp : (DigraphOrderedGraph D (rank τ))ᶜ.Adj (v i) (v j) :=
        hClique (hv_mem i) (hv_mem j) hne
      have hnot : ¬ (DigraphOrderedGraph D (rank τ)).Adj (v i) (v j) := by
        simpa using hcomp.2
      exact hnot (Or.inl ⟨hr_lt, hDij⟩)
    exact ⟨⟨v, hv_inj, hv_range, hv_strict, hv_fwd⟩⟩
  let sortedData : (τ : Equiv.Perm W) → (S : I τ) → SortedData τ S := fun τ S =>
    Classical.choice (sortedData_nonempty τ S)
  let sorted : (τ : Equiv.Perm W) → I τ → (Fin k → W) := fun τ S =>
    (sortedData τ S).1
  have sorted_spec : ∀ (τ : Equiv.Perm W) (S : I τ),
      Function.Injective (sorted τ S) ∧
        Set.range (sorted τ S) = (↑(S : Finset W) : Set W) ∧
          StrictMono (fun i : Fin k => rank τ (sorted τ S i)) ∧
            ForwardIndependentTuple D (sorted τ S) := by
    intro τ S
    exact (sortedData τ S).2
  let A : Type u :=
    Sigma fun τ : Equiv.Perm W => I τ × Equiv.Perm (Fin k)
  let B : Type u :=
    {v : Fin k → W // ForwardIndependentTuple D v} × Equiv.Perm W
  have hcard_le : Fintype.card A ≤ Fintype.card B := by
    let toB : A → B := fun a =>
      let τ : Equiv.Perm W := a.1
      let S : I τ := a.2.1
      let σ : Equiv.Perm (Fin k) := a.2.2
      let emb : Fin k ↪ W := ⟨sorted τ S, (sorted_spec τ S).1⟩
      (⟨sorted τ S, (sorted_spec τ S).2.2.2⟩,
        (σ.viaFintypeEmbedding emb).trans τ)
    have htoB_inj : Function.Injective toB := by
      intro a b hab
      rcases a with ⟨τa, Sa, σa⟩
      rcases b with ⟨τb, Sb, σb⟩
      dsimp [toB] at hab
      have hsort : sorted τa Sa = sorted τb Sb := by
        exact congrArg (fun x : B => ((x.1 : {v : Fin k → W // ForwardIndependentTuple D v}).1)) hab
      have hperm :
          (σa.viaFintypeEmbedding (⟨sorted τa Sa, (sorted_spec τa Sa).1⟩ : Fin k ↪ W)).trans τa =
            (σb.viaFintypeEmbedding (⟨sorted τb Sb, (sorted_spec τb Sb).1⟩ : Fin k ↪ W)).trans τb := by
        exact congrArg Prod.snd hab
      let emb_a : Fin k ↪ W := ⟨sorted τa Sa, (sorted_spec τa Sa).1⟩
      let emb_b : Fin k ↪ W := ⟨sorted τb Sb, (sorted_spec τb Sb).1⟩
      let π : Equiv.Perm W := (σa.viaFintypeEmbedding emb_a).trans τa
      let v : Fin k → W := sorted τa Sa
      let Inc :=
        {σ : Equiv.Perm (Fin k) // StrictMono (fun i : Fin k => baseRank (π (v (σ i))))}
      have hinca : StrictMono (fun i : Fin k => baseRank (π (v (σa.symm i)))) := by
        have hs := (sorted_spec τa Sa).2.2.1
        intro i j hij
        have hlt := hs hij
        have happ_i :
            (σa.viaFintypeEmbedding emb_a) (sorted τa Sa (σa.symm i)) =
              sorted τa Sa i := by
          change (σa.viaFintypeEmbedding emb_a) (emb_a (σa.symm i)) = emb_a i
          rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
          simp
        have happ_j :
            (σa.viaFintypeEmbedding emb_a) (sorted τa Sa (σa.symm j)) =
              sorted τa Sa j := by
          change (σa.viaFintypeEmbedding emb_a) (emb_a (σa.symm j)) = emb_a j
          rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
          simp
        calc
          baseRank (π (v (σa.symm i))) = rank τa (sorted τa Sa i) := by
            simp [π, v, rank, happ_i]
          _ < rank τa (sorted τa Sa j) := hlt
          _ = baseRank (π (v (σa.symm j))) := by
            simp [π, v, rank, happ_j]
      have hincb : StrictMono (fun i : Fin k => baseRank (π (v (σb.symm i)))) := by
        have hs := (sorted_spec τb Sb).2.2.1
        intro i j hij
        have hlt := hs hij
        let πb : Equiv.Perm W := (σb.viaFintypeEmbedding emb_b).trans τb
        have hπ : π = πb := by
          simpa [π, πb, emb_a, emb_b] using hperm
        have hv_i : v (σb.symm i) = sorted τb Sb (σb.symm i) := by
          simp [v, hsort]
        have hv_j : v (σb.symm j) = sorted τb Sb (σb.symm j) := by
          simp [v, hsort]
        have happ_i :
            (σb.viaFintypeEmbedding emb_b) (sorted τb Sb (σb.symm i)) =
              sorted τb Sb i := by
          change (σb.viaFintypeEmbedding emb_b) (emb_b (σb.symm i)) = emb_b i
          rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
          simp
        have happ_j :
            (σb.viaFintypeEmbedding emb_b) (sorted τb Sb (σb.symm j)) =
              sorted τb Sb j := by
          change (σb.viaFintypeEmbedding emb_b) (emb_b (σb.symm j)) = emb_b j
          rw [Equiv.Perm.viaFintypeEmbedding_apply_image]
          simp
        calc
          baseRank (π (v (σb.symm i))) = rank τb (sorted τb Sb i) := by
            rw [hπ, hv_i]
            simp [πb, rank, happ_i]
          _ < rank τb (sorted τb Sb j) := hlt
          _ = baseRank (π (v (σb.symm j))) := by
            rw [hπ, hv_j]
            simp [πb, rank, happ_j]
      have htuple_inj : Function.Injective (fun i : Fin k => π (v i)) :=
        π.injective.comp (sorted_spec τa Sa).1
      have hbase_on : Set.InjOn baseRank (Set.range (fun i : Fin k => π (v i))) := by
        intro x _ y _ hxy
        exact hbase_inj hxy
      have hfiber :=
        TupleIncreasingPermutationFiberCount
          (v := fun i : Fin k => π (v i)) (r := baseRank) htuple_inj hbase_on
      have hfiber' : Nat.factorial k * Fintype.card Inc = Nat.factorial k := by
        simpa [Inc, Fintype.card_perm, Fintype.card_fin] using hfiber
      have hcardInc : Fintype.card Inc = 1 :=
        Nat.mul_left_cancel (Nat.factorial_pos k) (by simpa using hfiber')
      have hsub : Subsingleton Inc :=
        (Fintype.card_le_one_iff_subsingleton).mp (by rw [hcardInc])
      have hsym : σa.symm = σb.symm := by
        have hsubeq : (⟨σa.symm, hinca⟩ : Inc) = ⟨σb.symm, hincb⟩ :=
          Subsingleton.elim _ _
        exact congrArg Subtype.val hsubeq
      have hσ : σa = σb := by
        have hs := congrArg Equiv.symm hsym
        simpa using hs
      have hemb : emb_a = emb_b := by
        ext i
        exact congrFun hsort i
      have hτ : τa = τb := by
        subst σb
        have hperm' :
            (σa.viaFintypeEmbedding emb_a).trans τa =
              (σa.viaFintypeEmbedding emb_a).trans τb := by
          simpa [emb_a, emb_b, hsort] using hperm
        apply Equiv.ext
        intro x
        have hx := congrFun (congrArg Equiv.toFun hperm')
          ((σa.viaFintypeEmbedding emb_a).symm x)
        simpa using hx
      subst τb
      subst σb
      have hSset : (↑(Sa : Finset W) : Set W) = (↑(Sb : Finset W) : Set W) := by
        calc
          (↑(Sa : Finset W) : Set W) = Set.range (sorted τa Sa) :=
            ((sorted_spec τa Sa).2.1).symm
          _ = Set.range (sorted τa Sb) := by rw [hsort]
          _ = (↑(Sb : Finset W) : Set W) :=
            (sorted_spec τa Sb).2.1
      have hS : Sa = Sb := by
        apply Subtype.ext
        apply Finset.ext
        intro x
        have hx := congrArg (fun T : Set W => x ∈ T) hSset
        simpa using hx
      subst Sb
      rfl
    exact Fintype.card_le_of_embedding ⟨toB, htoB_inj⟩
  have hsum_le :
      (∑ τ : Equiv.Perm W,
          Nat.factorial k *
            SimpleGraphIndependentSetCount (DigraphOrderedGraph D (rank τ)) k) ≤
        ∑ _τ : Equiv.Perm W, ForwardIndependentTupleCount D k := by
    simpa [A, B, I, SimpleGraphIndependentSetCount, ForwardIndependentTupleCount,
      Fintype.card_sigma, Fintype.card_prod, Fintype.card_perm, Fintype.card_fin,
      Finset.sum_const, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hcard_le
  have hnon : (Finset.univ : Finset (Equiv.Perm W)).Nonempty :=
    ⟨Equiv.refl W, Finset.mem_univ _⟩
  rcases Finset.exists_le_of_sum_le
      (s := (Finset.univ : Finset (Equiv.Perm W)))
      (f := fun τ : Equiv.Perm W =>
        Nat.factorial k *
          SimpleGraphIndependentSetCount (DigraphOrderedGraph D (rank τ)) k)
      (g := fun _τ : Equiv.Perm W => ForwardIndependentTupleCount D k)
      hnon (by simpa using hsum_le) with
    ⟨τ, _hτmem, hτbound⟩
  exact ⟨rank τ, hτbound⟩
