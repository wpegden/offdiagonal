import Tablet.DigraphLoopless
import Tablet.RandomHomomorphismColoring
import Tablet.TransitiveTournamentFree

-- [TABLET NODE: RandomHomomorphismFirstColorOrderedCliqueFree]

theorem RandomHomomorphismFirstColorOrderedCliqueFree {W : Type}
    (D : Digraph W) (s ell n : ℕ) (hell : 1 ≤ ell)
    (hloopless : DigraphLoopless D) (hfree : TransitiveTournamentFree D s)
    (phi : Fin (ell - 1) → Fin n → W) :
    ∀ (c : Fin (ell - 1)) (v : Fin s → Fin n), StrictMono v →
      ¬ (∀ i j : Fin s, i < j →
        RandomHomomorphismColoring D ell n hell phi (Sym2.mk (v i) (v j)) =
          (⟨c.val, by omega⟩ : Fin ell)) := by
-- BODY
  classical
  have firstColorArc :
      ∀ (x y : Fin n) (hxy : x ≤ y) (c : Fin (ell - 1)),
        RandomHomomorphismColoring D ell n hell phi (Sym2.mk x y) =
            (⟨c.val, by omega⟩ : Fin ell) →
          D (phi c x) (phi c y) := by
    intro x y hxy c hcolor
    have hsorted :
        D (phi c (min x y)) (phi c (max x y)) := by
      dsimp [RandomHomomorphismColoring] at hcolor
      by_cases h : ∃ m : ℕ, ∃ hm : m < ell - 1,
          D (phi ⟨m, hm⟩ (min x y)) (phi ⟨m, hm⟩ (max x y))
      · simp [h] at hcolor
        let m : ℕ := Nat.find h
        have hm_lt : m < ell - 1 := Classical.choose (Nat.find_spec h)
        have hm_arc :
            D (phi ⟨m, hm_lt⟩ (min x y)) (phi ⟨m, hm_lt⟩ (max x y)) :=
          Classical.choose_spec (Nat.find_spec h)
        have hm_eq : m = c.val := by
          simpa [m] using hcolor
        have hfin : (⟨m, hm_lt⟩ : Fin (ell - 1)) = c := by
          ext
          exact hm_eq
        simpa [hfin] using hm_arc
      · simp [h] at hcolor
        omega
    simpa [min_eq_left hxy, max_eq_right hxy] using hsorted
  intro c v hv hmono
  apply hfree
  refine ⟨fun i => phi c (v i), ?_, ?_⟩
  · intro i j hij_eq
    by_cases hijlt : i < j
    · exfalso
      have harc := firstColorArc (v i) (v j) (le_of_lt (hv hijlt)) c (hmono i j hijlt)
      exact hloopless (phi c (v i)) (by simpa [hij_eq] using harc)
    · by_cases hjilt : j < i
      · exfalso
        have harc := firstColorArc (v j) (v i) (le_of_lt (hv hjilt)) c (hmono j i hjilt)
        exact hloopless (phi c (v i)) (by simpa [hij_eq] using harc)
      · exact le_antisymm (le_of_not_gt hjilt) (le_of_not_gt hijlt)
  · intro i j hij
    exact firstColorArc (v i) (v j) (le_of_lt (hv hij)) c (hmono i j hij)
