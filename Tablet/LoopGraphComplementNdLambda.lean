import Tablet.LoopGraphComplement
import Tablet.LoopGraphNdLambda

-- [TABLET NODE: LoopGraphComplementNdLambda]

universe u

theorem LoopGraphComplementNdLambda {V : Type u} [Fintype V]
    (G : LoopGraph V) (n d : ℕ) (lambda : ℝ)
    (hG : LoopGraphNdLambda G n d lambda) :
    LoopGraphNdLambda (LoopGraphComplement G) n (n - d) lambda := by
-- BODY
  classical
  rcases hG with ⟨hcard, hsymm, hdeg, heig, hlambda⟩
  refine ⟨hcard, ?_, ?_, ?_, hlambda⟩
  · intro x y hxy hyx
    exact hxy (hsymm hyx)
  · intro v
    dsimp [LoopGraphDegree, LoopGraphComplement]
    have hsum := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset V)) (p := fun w => G v w)
    have hfilter : (Finset.univ.filter fun w => G v w).card = d := by
      simpa [LoopGraphDegree] using hdeg v
    have htotal : (Finset.univ : Finset V).card = n := by
      simpa using hcard
    have hcompl : (Finset.univ.filter (fun a : V => ¬ G v a)).card = n - d :=
      Nat.eq_sub_of_add_eq (by
        simpa [hfilter, htotal, Nat.add_comm] using hsum)
    rw [← hcompl]
    exact congrArg Finset.card (by
      ext w
      simp)
  · intro mu hmu
    rcases hmu with ⟨f, hnonzero, hzero, heq⟩
    have hcomp_action :
        ∀ v : V, LoopGraphAdjacencyAction (LoopGraphComplement G) f v =
          - LoopGraphAdjacencyAction G f v := by
      intro v
      dsimp [LoopGraphAdjacencyAction, LoopGraphComplement]
      change (∑ w : V, if LoopGraphComplement G v w then f w else 0) =
        -∑ w : V, if G v w then f w else 0
      have hpoint :
          ∀ w : V, (if LoopGraphComplement G v w then f w else 0) =
            f w - (if G v w then f w else 0) := by
        intro w
        by_cases hw : G v w <;> simp [LoopGraphComplement, hw]
      calc
        (∑ w, if LoopGraphComplement G v w then f w else 0)
            = ∑ w, (f w - (if G v w then f w else 0)) := by
              exact Finset.sum_congr rfl (fun w _ => hpoint w)
        _ = (∑ w, f w) - ∑ w, if G v w then f w else 0 := by
              rw [Finset.sum_sub_distrib]
        _ = -∑ w, if G v w then f w else 0 := by
              rw [hzero]
              ring
    have hG_eig : LoopGraphNonprincipalEigenvalue G (-mu) := by
      refine ⟨f, hnonzero, hzero, ?_⟩
      intro v
      have hv := heq v
      rw [hcomp_action v] at hv
      linarith
    have hbound := heig (-mu) hG_eig
    simpa [abs_neg] using hbound
