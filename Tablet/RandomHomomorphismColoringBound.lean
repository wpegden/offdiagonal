import Tablet.F2ForwardIndependentNearDiagonalBound
import Tablet.NoMonochromaticCliqueColoring
import Tablet.RandomHomomorphismColoring
import Tablet.RandomHomomorphismF2Setup
import Tablet.RandomHomomorphismFinalColorArithmetic
import Tablet.RandomHomomorphismFinalColorBadCountStrict
import Tablet.RandomHomomorphismFinalColorCliqueToForwardIndependent
import Tablet.RandomHomomorphismFinalColorForwardIndependent
import Tablet.RandomHomomorphismFinalColorSelectionFromCount
import Tablet.RandomHomomorphismFirstColorOrderedCliqueFree

-- [TABLET NODE: RandomHomomorphismColoringBound]

theorem RandomHomomorphismColoringBound :
    ∀ ell : ℕ, 3 ≤ ell → ∃ s0 : ℕ, ∀ s n : ℕ, s0 ≤ s →
      (n : ℝ) ≤ Real.rpow 2 (((s : ℝ) / 2 - 4) * ((ell - 1 : ℕ) : ℝ)) →
        ∃ color : Sym2 (Fin n) → Fin ell,
          NoMonochromaticCliqueColoring s ell n color := by
-- BODY
  intro ell hell
  rcases RandomHomomorphismF2Setup with ⟨s0, hs0_four, hsetup⟩
  refine ⟨s0, ?_⟩
  intro s n hs hn
  by_cases hsn : s ≤ n
  · rcases hsetup s hs with
      ⟨W, instW, D, hloopless, hfree, _hcardW, hWlower, hFbound⟩
    letI : Fintype W := instW
    have hs4 : 4 ≤ s := le_trans hs0_four hs
    have hbad_count :
        let Ω := Fin (ell - 1) → Fin n → W
        let Bad : Ω → Prop := fun phi =>
          ∃ S : Finset (Fin n), S.card = s ∧
            ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v →
              RandomHomomorphismColoring D ell n (by omega) phi (Sym2.mk u v) =
                (⟨ell - 1, by omega⟩ : Fin ell)
        Fintype.card {phi : Ω // Bad phi} < Fintype.card Ω :=
      RandomHomomorphismFinalColorBadCountStrict D s ell n hell hs4 hsn hWlower hFbound hn
    rcases RandomHomomorphismFinalColorSelectionFromCount D s ell n hell hbad_count with
      ⟨phi, hphi_good⟩
    refine ⟨RandomHomomorphismColoring D ell n (by omega) phi, ?_⟩
    intro hmono
    rcases hmono with ⟨S, hS_card, c, hS_mono⟩
    by_cases hcfinal : c = (⟨ell - 1, by omega⟩ : Fin ell)
    · apply hphi_good
      refine ⟨S, hS_card, ?_⟩
      intro u v hu hv huv
      simpa [hcfinal] using hS_mono u v hu hv huv
    · have hc_lt : c.val < ell - 1 := by
        have hcne_val : c.val ≠ ell - 1 := by
          intro hval
          apply hcfinal
          ext
          exact hval
        omega
      let cfirst : Fin (ell - 1) := ⟨c.val, hc_lt⟩
      let v : Fin s → Fin n := S.orderEmbOfFin hS_card
      have hv : StrictMono v := (S.orderEmbOfFin hS_card).strictMono
      have hordered :
          ∀ i j : Fin s, i < j →
            RandomHomomorphismColoring D ell n (by omega) phi (Sym2.mk (v i) (v j)) =
              (⟨cfirst.val, by omega⟩ : Fin ell) := by
        intro i j hij
        have hcol := hS_mono (v i) (v j)
          (Finset.orderEmbOfFin_mem S hS_card i)
          (Finset.orderEmbOfFin_mem S hS_card j)
          (ne_of_lt (hv hij))
        have hc_eq : c = (⟨cfirst.val, by omega⟩ : Fin ell) := by
          ext
          rfl
        simpa [hc_eq] using hcol
      exact RandomHomomorphismFirstColorOrderedCliqueFree
        D s ell n (by omega) hloopless hfree phi cfirst v hv hordered
  · refine ⟨fun _ => (⟨0, by omega⟩ : Fin ell), ?_⟩
    intro hmono
    rcases hmono with ⟨S, hS_card, _c, _hS_mono⟩
    have hS_le_n : S.card ≤ n := by
      simpa [Fintype.card_fin] using Finset.card_le_univ S
    omega
