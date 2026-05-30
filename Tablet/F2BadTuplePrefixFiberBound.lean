import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTuplePrefixFiberBound]

theorem F2BadTuplePrefixFiberBound (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) (i : ℕ) :
    Fintype.card
        {y : Fin p → ZMod 2 //
          ∀ j : {j : Fin k // j.val < i}, (ab j.1).1 ⬝ᵥ y = 1} ≤
      2 ^ (p - F2BadTupleRank p k ab i) := by
-- BODY
  classical
  let V : Type := Fin p → ZMod 2
  let J : Type := {j : Fin k // j.val < i}
  let A : J → V := fun j => (ab j.1).1
  let S : Submodule (ZMod 2) V :=
    Submodule.span (ZMod 2) (Set.range A)
  let dualEquiv : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
    (Pi.basisFun (ZMod 2) (Fin p)).toDualEquiv
  let Phi : Submodule (ZMod 2) (Module.Dual (ZMod 2) V) :=
    S.map (dualEquiv : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)
  let Sol : Type :=
    {y : V // ∀ j : J, A j ⬝ᵥ y = 1}
  have hdual_apply : ∀ a y : V, dualEquiv a y = a ⬝ᵥ y := by
    intro a y
    simp [dualEquiv, V, Module.Basis.toDualEquiv_apply, Module.Basis.toDual, dotProduct,
      Pi.basisFun]
  have hcard_Phi :
      Fintype.card Phi.dualCoannihilator =
        2 ^ (p - F2BadTupleRank p k ab i) := by
    have hfinPhi : Module.finrank (ZMod 2) Phi = F2BadTupleRank p k ab i := by
      dsimp [F2BadTupleRank]
      change Module.finrank (ZMod 2)
          (S.map (dualEquiv : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V)) =
        Module.finrank (ZMod 2) S
      exact LinearEquiv.finrank_map_eq dualEquiv S
    have hfinV : Module.finrank (ZMod 2) V = p := by
      rw [Module.finrank_fin_fun]
    have hsum :=
      Subspace.finrank_add_finrank_dualCoannihilator_eq
        (K := ZMod 2) (V := V) Phi
    have hfinCo :
        Module.finrank (ZMod 2) Phi.dualCoannihilator =
          p - F2BadTupleRank p k ab i := by
      omega
    rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := Phi.dualCoannihilator),
      hfinCo]
    norm_num [ZMod.card]
  have hcard_le :
      Fintype.card Sol ≤ Fintype.card Phi.dualCoannihilator := by
    by_cases hnonempty : Nonempty Sol
    · rcases hnonempty with ⟨y0⟩
      refine Fintype.card_le_of_injective
        (fun y : Sol => (⟨y.1 - y0.1, ?_⟩ : Phi.dualCoannihilator)) ?_
      · rw [Submodule.mem_dualCoannihilator]
        intro f hf
        rcases hf with ⟨x, hxS, rfl⟩
        refine Submodule.span_induction (s := Set.range A)
          (p := fun x hx => (dualEquiv x) (y.1 - y0.1) = 0) ?_ ?_ ?_ ?_ hxS
        · rintro x ⟨j, rfl⟩
          rw [hdual_apply, dotProduct_sub, y.2 j, y0.2 j, sub_self]
        · simp
        · intro x z hx hz hx0 hz0
          simp [map_add, hx0, hz0]
        · intro c x hx hx0
          simp [map_smul, hx0]
      · intro y z hyz
        apply Subtype.ext
        have hval := congrArg Subtype.val hyz
        exact sub_left_injective hval
    · haveI : IsEmpty Sol := not_nonempty_iff.mp hnonempty
      simp
  change Fintype.card Sol ≤ 2 ^ (p - F2BadTupleRank p k ab i)
  exact hcard_le.trans_eq hcard_Phi
