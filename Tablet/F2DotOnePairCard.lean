import Mathlib.Algebra.Field.ZMod
import Tablet.Preamble

-- [TABLET NODE: F2DotOnePairCard]

theorem F2DotOnePairCard (p : ℕ) :
    Fintype.card {z : ((Fin p → ZMod 2) × (Fin p → ZMod 2)) // z.1 ⬝ᵥ z.2 = 1}
      = (2 ^ p - 1) * 2 ^ (p - 1) := by
-- BODY
  classical
  let Vec : Type := Fin p → ZMod 2
  let Nonzero : Type := {x : Vec // x ≠ 0}
  let Fiber : Nonzero → Type := fun x => {y : Vec // x.val ⬝ᵥ y = 1}
  have hU_equiv :
      {z : Vec × Vec // z.1 ⬝ᵥ z.2 = 1} ≃ Sigma Fiber := {
    toFun z := by
      refine ⟨⟨z.val.1, ?_⟩, ⟨z.val.2, z.property⟩⟩
      intro hx
      have hzero : (0 : ZMod 2) = 1 := by
        simpa [Vec, hx, dotProduct] using z.property
      exact zero_ne_one hzero
    invFun z := ⟨(z.1.val, z.2.val), z.2.property⟩
    left_inv z := by
      rfl
    right_inv z := by
      cases z with
      | mk x y =>
        cases x
        cases y
        rfl }
  have hfiber_card : ∀ x : Nonzero, Fintype.card (Fiber x) = 2 ^ (p - 1) := by
    intro x
    obtain ⟨i, hxi⟩ : ∃ i : Fin p, x.val i ≠ 0 := by
      by_contra h
      have hxzero : x.val = 0 := by
        funext i
        by_contra hi
        exact h ⟨i, hi⟩
      exact x.property hxzero
    let drop : Fiber x → ({ j : Fin p // j ≠ i } → ZMod 2) := fun y j => y.1 j.1
    let extend : ({ j : Fin p // j ≠ i } → ZMod 2) → Fiber x := fun z =>
      ⟨fun j => if hji : j = i then
          ((1 - ∑ k : { j : Fin p // j ≠ i }, x.val k.1 * z k) / x.val i)
        else z ⟨j, hji⟩,
        by
          rw [dotProduct, Fintype.sum_eq_add_sum_subtype_ne
            (fun j => x.val j * (if hji : j = i then
              ((1 - ∑ k : { j : Fin p // j ≠ i }, x.val k.1 * z k) / x.val i)
            else z ⟨j, hji⟩)) i]
          simp [(fun k : { j : Fin p // j ≠ i } => k.property)]
          field_simp [hxi]
          ring⟩
    let eFiber : Fiber x ≃ ({ j : Fin p // j ≠ i } → ZMod 2) := {
      toFun := drop
      invFun := extend
      left_inv := by
        intro y
        ext j
        by_cases hji : j = i
        · subst j
          dsimp [drop, extend]
          simp
          have hdot : x.val ⬝ᵥ (y : Vec) = 1 := y.property
          rw [dotProduct, Fintype.sum_eq_add_sum_subtype_ne
            (fun j => x.val j * (y : Vec) j) i] at hdot
          let S := ∑ k : { j : Fin p // j ≠ i }, x.val k.1 * (y : Vec) k.1
          have hmul : x.val i * (y : Vec) i = 1 - S := by
            rw [eq_sub_iff_add_eq]
            exact hdot
          field_simp [hxi]
          rw [← hmul]
        · dsimp [drop, extend]
          simp [hji]
      right_inv := by
        intro z
        funext j
        dsimp [drop, extend]
        simp [j.property] }
    have hcompl_card : Fintype.card { j : Fin p // j ≠ i } = p - 1 := by
      rw [Fintype.card_subtype_compl (fun j : Fin p => j = i)]
      simp
    calc
      Fintype.card (Fiber x)
          = Fintype.card ({ j : Fin p // j ≠ i } → ZMod 2) :=
            Fintype.card_congr eFiber
      _ = Fintype.card (ZMod 2) ^ Fintype.card { j : Fin p // j ≠ i } := by
            rw [Fintype.card_fun]
      _ = 2 ^ (p - 1) := by
            rw [hcompl_card, ZMod.card]
  have hnonzero_card : Fintype.card Nonzero = 2 ^ p - 1 := by
    have hvec_card : Fintype.card Vec = 2 ^ p := by
      dsimp [Vec]
      rw [Fintype.card_fun, Fintype.card_fin, ZMod.card]
    change Fintype.card {x : Vec // x ≠ 0} = 2 ^ p - 1
    rw [Fintype.card_subtype_compl (fun x : Vec => x = 0)]
    simp [hvec_card]
  calc
    Fintype.card {z : ((Fin p → ZMod 2) × (Fin p → ZMod 2)) // z.1 ⬝ᵥ z.2 = 1}
        = Fintype.card {z : Vec × Vec // z.1 ⬝ᵥ z.2 = 1} := by
          rfl
    _ = Fintype.card (Sigma Fiber) := Fintype.card_congr hU_equiv
    _ = ∑ x : Nonzero, Fintype.card (Fiber x) := by
          rw [Fintype.card_sigma]
    _ = ∑ _x : Nonzero, 2 ^ (p - 1) := by
          exact Finset.sum_congr rfl (fun x _ => hfiber_card x)
    _ = Fintype.card Nonzero * 2 ^ (p - 1) := by
          simp [Finset.sum_const]
    _ = (2 ^ p - 1) * 2 ^ (p - 1) := by
          rw [hnonzero_card]
