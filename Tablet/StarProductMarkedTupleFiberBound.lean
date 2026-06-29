import Mathlib.Tactic
import Tablet.BinarySequenceWeightSnoc
import Tablet.StarProductMarkedTupleFiberCount

-- [TABLET NODE: StarProductMarkedTupleFiberBound]

universe u

theorem StarProductMarkedTupleFiberBound {V : Type u}
    (G : LoopGraph V) [Fintype (ProductDigraphVertex G)]
    (k Delta h : ℕ)
    (marked : ∀ m : ℕ, (Fin m → ProductDigraphVertex G) → ProductDigraphVertex G → Bool)
    (hAll : ∀ (m : ℕ), m < k → ∀ p : Fin m → ProductDigraphVertex G,
      ForwardIndependentTuple (StarProductDigraph G) p →
        Nat.card {x : ProductDigraphVertex G //
          ForwardIndependentTuple (StarProductDigraph G)
            (@Fin.snoc m (fun _ => ProductDigraphVertex G) p x)} ≤ Delta)
    (hMarked : ∀ (m : ℕ), m < k → ∀ p : Fin m → ProductDigraphVertex G,
      ForwardIndependentTuple (StarProductDigraph G) p →
        Nat.card {x : ProductDigraphVertex G //
          ForwardIndependentTuple (StarProductDigraph G)
              (@Fin.snoc m (fun _ => ProductDigraphVertex G) p x) ∧
            marked m p x = true} ≤ h)
    (z : Fin k → Bool) :
    StarProductMarkedTupleFiberCount G marked z ≤
      Delta ^ BinarySequenceWeight z * h ^ (k - BinarySequenceWeight z) := by
-- BODY
  classical
  induction k with
  | zero =>
      simp only [StarProductMarkedTupleFiberCount, BinarySequenceWeight,
        Finset.univ_eq_empty, Finset.filter_empty, Finset.card_empty, pow_zero,
        tsub_zero, mul_one]
      refine Fintype.card_le_one_iff_subsingleton.mpr ?_
      exact ⟨fun x y => by
        apply Subtype.ext
        apply Subtype.ext
        funext i
        exact Fin.elim0 i⟩
  | succ m ih =>
      let W := ProductDigraphVertex G
      let D := StarProductDigraph G
      let sig {n : ℕ} (v : Fin n → W) :=
        StarProductMarkedTupleSignature G marked v
      let zp : Fin m → Bool := fun i => z i.castSucc
      let Full :=
        {p : {v : Fin (m + 1) → W // ForwardIndependentTuple D v} //
          sig p.1 = z}
      let Prefix :=
        {p : {v : Fin m → W // ForwardIndependentTuple D v} //
          sig p.1 = zp}
      let lastBit := z (Fin.last m)
      let Option (p : Prefix) :=
        {x : W // ForwardIndependentTuple D
            (@Fin.snoc m (fun _ => W) p.1.1 x) ∧
          (if lastBit = true then True else marked m p.1.1 x = true)}
      let Target :=
        {r : Prefix × W // ForwardIndependentTuple D
            (@Fin.snoc m (fun _ => W) r.1.1.1 r.2) ∧
          (if lastBit = true then True else marked m r.1.1.1 r.2 = true)}
      have hPrefix (v : Fin (m + 1) → W)
          (hv : ForwardIndependentTuple D v ∧ sig v = z) :
          ForwardIndependentTuple D (fun i : Fin m => v i.castSucc) ∧
            sig (fun i : Fin m => v i.castSucc) = zp := by
        constructor
        · intro i j hij
          exact hv.1 i.castSucc j.castSucc (by simpa using hij)
        · funext i
          have hsig := congr_fun hv.2 i.castSucc
          calc
            sig (fun i : Fin m => v i.castSucc) i =
                sig v i.castSucc := by
              simp [sig, StarProductMarkedTupleSignature]
            _ = z i.castSucc := hsig
            _ = zp i := rfl
      let encode : Full → Target := fun v =>
        let p : Prefix :=
          ⟨⟨fun i : Fin m => v.1.1 i.castSucc,
              (hPrefix v.1.1 ⟨v.1.2, v.2⟩).1⟩,
            (hPrefix v.1.1 ⟨v.1.2, v.2⟩).2⟩
        have hsnoc :
            (@Fin.snoc m (fun _ => W)
              (fun i : Fin m => v.1.1 i.castSucc)
              (v.1.1 (Fin.last m))) = v.1.1 := by
          funext i
          exact Fin.lastCases (by simp) (fun j => by simp) i
        have hfi :
            ForwardIndependentTuple D
              (@Fin.snoc m (fun _ => W) p.1.1 (v.1.1 (Fin.last m))) := by
          simpa [p, hsnoc] using v.1.2
        have hmark :
            (if lastBit = true then True
             else marked m p.1.1 (v.1.1 (Fin.last m)) = true) := by
          by_cases hlast_true : lastBit = true
          · simp [hlast_true]
          · have hlast_false : lastBit = false := by
              cases hbit : lastBit <;> simp [lastBit, hbit] at hlast_true ⊢
            have hsig_last := congr_fun v.2 (Fin.last m)
            have hnot :
                (! marked m p.1.1 (v.1.1 (Fin.last m))) = false := by
              simpa [sig, StarProductMarkedTupleSignature, p, lastBit,
                hlast_false] using hsig_last
            have hm : marked m p.1.1 (v.1.1 (Fin.last m)) = true := by
              cases hmarkbit : marked m p.1.1 (v.1.1 (Fin.last m)) <;>
                simp [hmarkbit] at hnot ⊢
            simp [hlast_true, hm]
        ⟨(p, v.1.1 (Fin.last m)), hfi, hmark⟩
      have hencode_inj : Function.Injective encode := by
        intro x y hxy
        dsimp [encode] at hxy
        have hval := congrArg Subtype.val hxy
        have hprefixSubtype : (Prod.fst (Subtype.val (encode x))) =
            (Prod.fst (Subtype.val (encode y))) := congrArg Prod.fst hval
        have hlast : (Prod.snd (Subtype.val (encode x))) =
            (Prod.snd (Subtype.val (encode y))) := congrArg Prod.snd hval
        dsimp [encode] at hprefixSubtype hlast
        have hprefix :
            (fun i : Fin m => x.1.1 i.castSucc) =
              (fun i : Fin m => y.1.1 i.castSucc) := by
          exact congrArg (fun p : Prefix => p.1.1) hprefixSubtype
        apply Subtype.ext
        apply Subtype.ext
        funext i
        exact Fin.lastCases (by simpa using hlast)
          (fun j => congr_fun hprefix j) i
      have hcard_full_target : Fintype.card Full ≤ Fintype.card Target :=
        Fintype.card_le_of_injective encode hencode_inj
      let targetEquiv : Target ≃ Sigma Option :=
        { toFun := fun r => ⟨r.1.1, ⟨r.1.2, r.2⟩⟩
          invFun := fun s => ⟨(s.1, s.2.1), s.2.2⟩
          left_inv := by
            intro r
            cases r with
            | mk val h =>
              cases val
              rfl
          right_inv := by
            intro s
            cases s with
            | mk p x =>
              cases x
              rfl }
      have hOptionEach :
          ∀ p : Prefix, Fintype.card (Option p) ≤
            (if lastBit = true then Delta else h) := by
        intro p
        by_cases hlast_true : lastBit = true
        · let forget : Option p →
            {x : W // ForwardIndependentTuple D
              (@Fin.snoc m (fun _ => W) p.1.1 x)} := fun x => ⟨x.1, x.2.1⟩
          have hforget_inj : Function.Injective forget := by
            intro x y hxy
            apply Subtype.ext
            exact congrArg (fun q : {x : W // ForwardIndependentTuple D
              (@Fin.snoc m (fun _ => W) p.1.1 x)} => q.1) hxy
          have hcard :
              Fintype.card (Option p) ≤
                Fintype.card {x : W // ForwardIndependentTuple D
                  (@Fin.snoc m (fun _ => W) p.1.1 x)} :=
            Fintype.card_le_of_injective forget hforget_inj
          exact hcard.trans (by
            rw [← Nat.card_eq_fintype_card]
            simpa [W, D, hlast_true] using
              hAll m (Nat.lt_succ_self m) p.1.1 p.1.2)
        · have hlast_false : lastBit = false := by
            cases hbit : lastBit <;> simp [lastBit, hbit] at hlast_true ⊢
          simpa [Option, W, D, hlast_false, hlast_true] using
            (by
              rw [← Nat.card_eq_fintype_card]
              exact hMarked m (Nat.lt_succ_self m) p.1.1 p.1.2)
      have htarget_card :
          Fintype.card Target ≤ Fintype.card Prefix *
            (if lastBit = true then Delta else h) := by
        calc
          Fintype.card Target = Fintype.card (Sigma Option) :=
              Fintype.card_congr targetEquiv
          _ = ∑ p : Prefix, Fintype.card (Option p) := Fintype.card_sigma
          _ ≤ ∑ _p : Prefix, (if lastBit = true then Delta else h) := by
              exact Finset.sum_le_sum (fun p _hp => hOptionEach p)
          _ = Fintype.card Prefix * (if lastBit = true then Delta else h) := by
              simp [mul_comm]
      have hfull_step :
          Fintype.card Full ≤ Fintype.card Prefix *
            (if lastBit = true then Delta else h) :=
        hcard_full_target.trans htarget_card
      have hAllPrefix : ∀ (n : ℕ), n < m → ∀ p : Fin n → ProductDigraphVertex G,
          ForwardIndependentTuple (StarProductDigraph G) p →
            Nat.card {x : ProductDigraphVertex G //
              ForwardIndependentTuple (StarProductDigraph G)
                (@Fin.snoc n (fun _ => ProductDigraphVertex G) p x)} ≤ Delta := by
        intro n hn p hp
        exact hAll n (Nat.lt_trans hn (Nat.lt_succ_self m)) p hp
      have hMarkedPrefix : ∀ (n : ℕ), n < m → ∀ p : Fin n → ProductDigraphVertex G,
          ForwardIndependentTuple (StarProductDigraph G) p →
            Nat.card {x : ProductDigraphVertex G //
              ForwardIndependentTuple (StarProductDigraph G)
                  (@Fin.snoc n (fun _ => ProductDigraphVertex G) p x) ∧
                marked n p x = true} ≤ h := by
        intro n hn p hp
        exact hMarked n (Nat.lt_trans hn (Nat.lt_succ_self m)) p hp
      have hprefix_bound :
          Fintype.card Prefix ≤
            Delta ^ BinarySequenceWeight zp * h ^ (m - BinarySequenceWeight zp) := by
        simpa [StarProductMarkedTupleFiberCount, Prefix, zp, sig, W, D] using
          ih hAllPrefix hMarkedPrefix zp
      have hweight_le : BinarySequenceWeight zp ≤ m := by
        simpa [BinarySequenceWeight] using
          (Finset.card_filter_le (Finset.univ : Finset (Fin m))
            (fun i : Fin m => zp i = true))
      have hfull_count :
          StarProductMarkedTupleFiberCount G marked z = Fintype.card Full := by
        simp [StarProductMarkedTupleFiberCount, Full, sig, W, D]
      rw [hfull_count]
      by_cases hlast_true : lastBit = true
      · have hweight :
            BinarySequenceWeight z = BinarySequenceWeight zp + 1 := by
          simpa [zp, lastBit, hlast_true] using BinarySequenceWeightSnoc z
        have hcombined :
            Fintype.card Full ≤
              (Delta ^ BinarySequenceWeight zp * h ^ (m - BinarySequenceWeight zp)) *
                Delta := by
          have hstep : Fintype.card Full ≤ Fintype.card Prefix * Delta := by
            simpa [hlast_true] using hfull_step
          exact hstep.trans (Nat.mul_le_mul_right Delta hprefix_bound)
        calc
          Fintype.card Full
              ≤ (Delta ^ BinarySequenceWeight zp * h ^ (m - BinarySequenceWeight zp)) *
                  Delta := hcombined
          _ = Delta ^ BinarySequenceWeight z * h ^ (m + 1 - BinarySequenceWeight z) := by
              rw [hweight]
              have hexp : m + 1 - (BinarySequenceWeight zp + 1) =
                  m - BinarySequenceWeight zp := by omega
              rw [hexp, pow_succ]
              ring
      · have hlast_false : lastBit = false := by
          cases hbit : lastBit <;> simp [lastBit, hbit] at hlast_true ⊢
        have hweight :
            BinarySequenceWeight z = BinarySequenceWeight zp := by
          simpa [zp, lastBit, hlast_false] using BinarySequenceWeightSnoc z
        have hcombined :
            Fintype.card Full ≤
              (Delta ^ BinarySequenceWeight zp * h ^ (m - BinarySequenceWeight zp)) *
                h := by
          have hstep :
              Fintype.card Full ≤ Fintype.card Prefix * h := by
            simpa [hlast_false, hlast_true] using hfull_step
          exact hstep.trans (Nat.mul_le_mul_right h hprefix_bound)
        calc
          Fintype.card Full
              ≤ (Delta ^ BinarySequenceWeight zp * h ^ (m - BinarySequenceWeight zp)) *
                  h := hcombined
          _ = Delta ^ BinarySequenceWeight z * h ^ (m + 1 - BinarySequenceWeight z) := by
              rw [hweight]
              have hexp : m + 1 - BinarySequenceWeight zp =
                  (m - BinarySequenceWeight zp) + 1 := by omega
              rw [hexp, pow_succ]
              ring
