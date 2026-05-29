import Tablet.ExpanderMixingLemma

-- [TABLET NODE: SparseNeighborhoodSetBound]

universe u

theorem SparseNeighborhoodSetBound {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) (hn : 0 < n) (hd : 0 < d) (A B : Finset V)
    (hA : ∀ u : V, u ∈ A ↔
      ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ) ≤
        ((d : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ))) :
    (A.card : ℝ) * (B.card : ℝ) ≤
      (4 : ℝ) * lambda ^ 2 / (d : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
-- BODY
  classical
  have h_edge_sum :
      LoopGraphEdgeCountBetween G A B =
        ∑ u ∈ A, LoopGraphEdgeCountBetween G ({u} : Finset V) B := by
    clear hA
    induction A using Finset.induction_on with
    | empty =>
        simp [LoopGraphEdgeCountBetween]
    | insert a A ha ih =>
        rw [Finset.sum_insert ha]
        rw [← ih]
        unfold LoopGraphEdgeCountBetween
        have hdisj :
            Disjoint
              (({a} ×ˢ B).filter (fun p : V × V => G p.1 p.2))
              ((A ×ˢ B).filter (fun p : V × V => G p.1 p.2)) := by
          rw [Finset.disjoint_left]
          intro p hp1 hp2
          simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_singleton] at hp1 hp2
          exact ha (by simpa [hp1.1.1] using hp2.1.1)
        have hfilter_eq :
            ((insert a A ×ˢ B).filter (fun p : V × V => G p.1 p.2)) =
              (({a} ×ˢ B).filter (fun p : V × V => G p.1 p.2)) ∪
                ((A ×ˢ B).filter (fun p : V × V => G p.1 p.2)) := by
          ext p
          constructor
          · intro hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
              Finset.mem_union, Finset.mem_singleton] at hp ⊢
            rcases hp.1.1 with hpa | hpA
            · exact Or.inl ⟨⟨hpa, hp.1.2⟩, hp.2⟩
            · exact Or.inr ⟨⟨hpA, hp.1.2⟩, hp.2⟩
          · intro hp
            simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert,
              Finset.mem_union, Finset.mem_singleton] at hp ⊢
            rcases hp with hp | hp
            · exact ⟨⟨Or.inl hp.1.1, hp.1.2⟩, hp.2⟩
            · exact ⟨⟨Or.inr hp.1.1, hp.1.2⟩, hp.2⟩
        change ((insert a A ×ˢ B).filter (fun p : V × V => G p.1 p.2)).card =
          (({a} ×ˢ B).filter (fun p : V × V => G p.1 p.2)).card +
            ((A ×ˢ B).filter (fun p : V × V => G p.1 p.2)).card
        rw [hfilter_eq, Finset.card_union_of_disjoint hdisj]
  let X : ℝ := (A.card : ℝ) * (B.card : ℝ)
  let m : ℝ := ((LoopGraphEdgeCountBetween G A B : ℕ) : ℝ)
  let q : ℝ := ((d : ℝ) / (n : ℝ)) * (A.card : ℝ) * (B.card : ℝ)
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hm_le_half : m ≤ q / 2 := by
    have hsum_le :
        (∑ u ∈ A, ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ)) ≤
          ∑ u ∈ A, (((d : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ))) := by
      refine Finset.sum_le_sum ?_
      intro u hu
      exact (hA u).mp hu
    have hm_eq :
        m =
          ∑ u ∈ A, ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ) := by
      simp [m, h_edge_sum, Nat.cast_sum]
    have hconst :
        (∑ u ∈ A, (((d : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ)))) =
          (A.card : ℝ) * (((d : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ))) := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
    calc
      m = ∑ u ∈ A, ((LoopGraphEdgeCountBetween G ({u} : Finset V) B : ℕ) : ℝ) := hm_eq
      _ ≤ ∑ u ∈ A, (((d : ℝ) * (B.card : ℝ)) / (2 * (n : ℝ))) := hsum_le
      _ = q / 2 := by
        rw [hconst]
        dsimp [q]
        field_simp [hnR.ne']
  have hq_nonneg : 0 ≤ q := by
    dsimp [q]
    positivity
  have habs_lower : q / 2 ≤ |m - q| := by
    have hmq : m ≤ q := by linarith
    have hnonpos : m - q ≤ 0 := by linarith
    have habs : |m - q| = q - m := by
      rw [abs_of_nonpos hnonpos]
      ring
    rw [habs]
    linarith
  have hmix := ExpanderMixingLemma (G := G) (n := n) (d := d) (lambda := lambda) hG A B
  have hmix_q : |m - q| ≤ lambda * Real.sqrt X := by
    simpa [m, q, X, mul_assoc] using hmix
  have hmain : q / 2 ≤ lambda * Real.sqrt X := le_trans habs_lower hmix_q
  by_cases hXzero : X = 0
  · calc
      (A.card : ℝ) * (B.card : ℝ) = 0 := hXzero
      _ ≤ (4 : ℝ) * lambda ^ 2 / (d : ℝ) ^ 2 * (n : ℝ) ^ 2 := by positivity
  · have hXnonneg : 0 ≤ X := by dsimp [X]; positivity
    have hXpos : 0 < X := lt_of_le_of_ne hXnonneg (Ne.symm hXzero)
    have hsqrt_pos : 0 < Real.sqrt X := (Real.sqrt_pos).2 hXpos
    have hq_eq : q / 2 = ((d : ℝ) * X) / (2 * (n : ℝ)) := by
      dsimp [q, X]
      field_simp [hnR.ne']
    have hmain' : ((d : ℝ) * X) / (2 * (n : ℝ)) ≤ lambda * Real.sqrt X := by
      simpa [hq_eq] using hmain
    have hlambda_nonneg : 0 ≤ lambda := by
      have hleft_pos : 0 < ((d : ℝ) * X) / (2 * (n : ℝ)) := by positivity
      have hright_pos : 0 < lambda * Real.sqrt X := lt_of_lt_of_le hleft_pos hmain'
      exact le_of_lt ((mul_pos_iff_of_pos_right hsqrt_pos).mp hright_pos)
    have hdiv_sqrt :
        ((d : ℝ) * Real.sqrt X) / (2 * (n : ℝ)) ≤ lambda := by
      have hraw : (((d : ℝ) * X) / (2 * (n : ℝ))) / Real.sqrt X ≤ lambda := by
        rw [div_le_iff₀ hsqrt_pos]
        simpa [mul_comm, mul_left_comm, mul_assoc] using hmain'
      have hlhs :
          (((d : ℝ) * X) / (2 * (n : ℝ))) / Real.sqrt X =
            ((d : ℝ) * Real.sqrt X) / (2 * (n : ℝ)) := by
        field_simp [hnR.ne', (ne_of_gt hsqrt_pos)]
        rw [Real.sq_sqrt hXnonneg]
      simpa [hlhs] using hraw
    have hlhs_nonneg : 0 ≤ ((d : ℝ) * Real.sqrt X) / (2 * (n : ℝ)) := by
      positivity
    have hsquare :
        (((d : ℝ) * Real.sqrt X) / (2 * (n : ℝ))) ^ 2 ≤ lambda ^ 2 := by
      rw [sq_le_sq]
      rw [abs_of_nonneg hlhs_nonneg, abs_of_nonneg hlambda_nonneg]
      exact hdiv_sqrt
    have hsquare' :
        ((d : ℝ) ^ 2 * X) / (4 * (n : ℝ) ^ 2) ≤ lambda ^ 2 := by
      convert hsquare using 1
      field_simp [hnR.ne']
      rw [Real.sq_sqrt hXnonneg]
      ring
    have hmult_nonneg : 0 ≤ (4 * (n : ℝ) ^ 2) / (d : ℝ) ^ 2 := by
      positivity
    have hmult := mul_le_mul_of_nonneg_right hsquare' hmult_nonneg
    calc
      (A.card : ℝ) * (B.card : ℝ) = X := rfl
      _ = (((d : ℝ) ^ 2 * X) / (4 * (n : ℝ) ^ 2)) *
            ((4 * (n : ℝ) ^ 2) / (d : ℝ) ^ 2) := by
          field_simp [hnR.ne', hdR.ne']
      _ ≤ lambda ^ 2 * ((4 * (n : ℝ) ^ 2) / (d : ℝ) ^ 2) := hmult
      _ = (4 : ℝ) * lambda ^ 2 / (d : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
          field_simp [hdR.ne']
