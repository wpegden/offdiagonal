import Tablet.ForwardIndependentTupleCount

-- [TABLET NODE: ForwardIndependentTupleCountSuccSnoc]

universe u

theorem ForwardIndependentTupleCountSuccSnoc {V : Type u} [Fintype V]
    (D : Digraph V) (m : ℕ) :
    ForwardIndependentTupleCount D (m + 1) =
      Nat.card
        {px : (Fin m → V) × V //
          ForwardIndependentTuple D
            (@Fin.snoc m (fun _ => V) px.1 px.2)} := by
-- BODY
  classical
  letI : DecidablePred (fun v : Fin (m + 1) → V => ForwardIndependentTuple D v) :=
    Classical.decPred _
  letI : DecidablePred
      (fun px : (Fin m → V) × V =>
        ForwardIndependentTuple D
          (@Fin.snoc m (fun _ => V) px.1 px.2)) :=
    Classical.decPred _
  let Full :=
    {v : Fin (m + 1) → V // ForwardIndependentTuple D v}
  let Snoc :=
    {px : (Fin m → V) × V //
      ForwardIndependentTuple D
        (@Fin.snoc m (fun _ => V) px.1 px.2)}
  let e : Full ≃ Snoc :=
    { toFun := fun v =>
        ⟨(fun i : Fin m => v.val i.castSucc, v.val (Fin.last m)), by
          have hv_eq :
              (@Fin.snoc m (fun _ => V)
                (fun i : Fin m => v.val i.castSucc) (v.val (Fin.last m))) =
                v.val := by
            funext i
            exact Fin.lastCases (by simp) (fun j => by simp) i
          rw [hv_eq]
          exact v.property⟩
      invFun := fun px =>
        ⟨@Fin.snoc m (fun _ => V) px.val.1 px.val.2, px.property⟩
      left_inv := by
        intro v
        apply Subtype.ext
        funext i
        exact Fin.lastCases (by simp) (fun j => by simp) i
      right_inv := by
        intro px
        cases px with
        | mk px hpx =>
          cases px with
          | mk pref x =>
            apply Subtype.ext
            apply Prod.ext
            · funext i
              simp
            · simp }
  calc
    ForwardIndependentTupleCount D (m + 1) = Fintype.card Full := by
      simp [ForwardIndependentTupleCount, Full]
    _ = Fintype.card Snoc := Fintype.card_congr e
    _ = Nat.card Snoc := (Nat.card_eq_fintype_card (α := Snoc)).symm
