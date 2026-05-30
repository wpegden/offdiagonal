import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Powerset
import Tablet.ForwardIndependentTupleCount
import Tablet.RandomHomomorphismFinalColorForwardIndependent

-- [TABLET NODE: RandomHomomorphismFinalColorBadCountUpper]

theorem RandomHomomorphismFinalColorBadCountUpper {W : Type} [Fintype W]
    (D : Digraph W) (s ell n : ℕ) (hell : 3 ≤ ell) :
    let Ω := Fin (ell - 1) → Fin n → W
    let Bad : Ω → Prop := fun phi =>
      ∃ S : Finset (Fin n), S.card = s ∧
        ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v →
          RandomHomomorphismColoring D ell n (by omega) phi (Sym2.mk u v) =
            (⟨ell - 1, by omega⟩ : Fin ell)
    Fintype.card {phi : Ω // Bad phi} ≤
      Nat.choose n s *
        (ForwardIndependentTupleCount D s) ^ (ell - 1) *
          (Fintype.card W) ^ ((ell - 1) * (n - s)) := by
-- BODY
  classical
  intro Ω Bad
  let BadWithSet :=
    {p : Ω × {S : Finset (Fin n) // S.card = s} //
      ∀ u v : Fin n, u ∈ p.2.1 → v ∈ p.2.1 → u ≠ v →
        RandomHomomorphismColoring D ell n (by omega) p.1 (Sym2.mk u v) =
          (⟨ell - 1, by omega⟩ : Fin ell)}
  have h_bad_to_pair :
      Fintype.card {phi : Ω // Bad phi} ≤ Fintype.card BadWithSet := by
    refine Fintype.card_le_of_injective
      (fun phiBad : {phi : Ω // Bad phi} =>
        (⟨(phiBad.1,
            ⟨Classical.choose phiBad.2,
              (Classical.choose_spec phiBad.2).1⟩),
          (Classical.choose_spec phiBad.2).2⟩ : BadWithSet)) ?_
    intro a b h
    apply Subtype.ext
    exact congrArg (fun x : BadWithSet => x.1.1) h
  let Enc :=
    Sigma (fun S : {S : Finset (Fin n) // S.card = s} =>
      (Fin (ell - 1) → {v : Fin s → W // ForwardIndependentTuple D v}) ×
        (Fin (ell - 1) → {x : Fin n // (x : Fin n) ∉ S.1} → W))
  have h_pair_to_enc : Fintype.card BadWithSet ≤ Fintype.card Enc := by
    refine Fintype.card_le_of_injective
      (fun p : BadWithSet =>
        let S : {S : Finset (Fin n) // S.card = s} := p.1.2
        let v : Fin s → Fin n := S.1.orderEmbOfFin S.2
        ⟨S,
          (fun c : Fin (ell - 1) =>
            ⟨fun i : Fin s => p.1.1 c (v i),
              by
                have hv : StrictMono v := (S.1.orderEmbOfFin S.2).strictMono
                have hfinal_ordered :
                    ∀ i j : Fin s, i < j →
                      RandomHomomorphismColoring D ell n (by omega) p.1.1
                          (Sym2.mk (v i) (v j)) =
                        (⟨ell - 1, by omega⟩ : Fin ell) := by
                  intro i j hij
                  exact p.2 (v i) (v j)
                    (Finset.orderEmbOfFin_mem S.1 S.2 i)
                    (Finset.orderEmbOfFin_mem S.1 S.2 j)
                    (ne_of_lt (hv hij))
                exact RandomHomomorphismFinalColorForwardIndependent
                  D s ell n (by omega) p.1.1 v hv hfinal_ordered c⟩),
          (fun c x => p.1.1 c x.1)⟩) ?_
    intro p q h
    rcases p with ⟨⟨phi, S⟩, hp⟩
    rcases q with ⟨⟨psi, T⟩, hq⟩
    dsimp at h ⊢
    have hS : S = T := congrArg Sigma.fst h
    subst T
    injection h with _ hcomp
    apply Subtype.ext
    apply Prod.ext
    · ext c x
      by_cases hx : x ∈ (S : Finset (Fin n))
      · have hxrange : x ∈ Set.range (S.1.orderEmbOfFin S.2) := by
          rw [Finset.range_orderEmbOfFin S.1 S.2]
          exact hx
        rcases hxrange with ⟨i, rfl⟩
        have htuples := congrArg (fun z => (z.1 c).1 i) hcomp
        exact htuples
      · have hout := congrArg
          (fun z => z.2 c (⟨x, hx⟩ : {x : Fin n // (x : Fin n) ∉ S.1})) hcomp
        exact hout
    · simp
  have henc_card :
      Fintype.card Enc =
        Nat.choose n s *
          (ForwardIndependentTupleCount D s) ^ (ell - 1) *
            (Fintype.card W) ^ ((ell - 1) * (n - s)) := by
    have hAcard :
        Fintype.card (Fin (ell - 1) →
            {v : Fin s → W // ForwardIndependentTuple D v}) =
          (ForwardIndependentTupleCount D s) ^ (ell - 1) := by
      rw [Fintype.card_fun, Fintype.card_fin]
      simp [ForwardIndependentTupleCount]
    have hBcard :
        ∀ S : {S : Finset (Fin n) // S.card = s},
          Fintype.card (Fin (ell - 1) →
              {x : Fin n // (x : Fin n) ∉ S.1} → W) =
            (Fintype.card W) ^ ((ell - 1) * (n - s)) := by
      intro S
      have hcompl :
          Fintype.card {x : Fin n // (x : Fin n) ∉ S.1} = n - s := by
        calc
          Fintype.card {x : Fin n // (x : Fin n) ∉ S.1}
              = Fintype.card (Fin n) -
                  Fintype.card {x : Fin n // (x : Fin n) ∈ S.1} := by
                rw [Fintype.card_subtype_compl (fun x : Fin n => (x : Fin n) ∈ S.1)]
          _ = n - s := by
                have hsub :
                    Fintype.card {x : Fin n // (x : Fin n) ∈ S.1} = s := by
                  rw [Fintype.card_subtype]
                  simp [S.2]
                rw [Fintype.card_fin, hsub]
      rw [Fintype.card_fun, Fintype.card_fin]
      rw [Fintype.card_fun, hcompl]
      rw [← pow_mul]
      congr 1
      rw [Nat.mul_comm]
    rw [Fintype.card_sigma]
    simp [Fintype.card_prod, hAcard, hBcard, Fintype.card_finset_len,
      Fintype.card_fin, mul_assoc]
  exact h_bad_to_pair.trans (h_pair_to_enc.trans_eq henc_card)

