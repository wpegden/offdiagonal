import Tablet.RandomHomomorphismColoring

-- [TABLET NODE: RandomHomomorphismFinalColorSelectionFromCount]

theorem RandomHomomorphismFinalColorSelectionFromCount {W : Type} [Fintype W]
    (D : Digraph W) (s ell n : ℕ) (hell : 3 ≤ ell) :
    let Ω := Fin (ell - 1) → Fin n → W
    let Bad : Ω → Prop := fun phi =>
      ∃ S : Finset (Fin n), S.card = s ∧
        ∀ u v : Fin n, u ∈ S → v ∈ S → u ≠ v →
          RandomHomomorphismColoring D ell n (by omega) phi (Sym2.mk u v) =
            (⟨ell - 1, by omega⟩ : Fin ell)
    Fintype.card {phi : Ω // Bad phi} < Fintype.card Ω →
      ∃ phi : Ω, ¬ Bad phi := by
-- BODY
  intro Ω Bad hbad
  classical
  by_contra hnot
  push Not at hnot
  have hle : Fintype.card Ω ≤ Fintype.card {phi : Ω // Bad phi} := by
    refine Fintype.card_le_of_injective
      (fun phi : Ω => (⟨phi, hnot phi⟩ : {phi : Ω // Bad phi})) ?_
    intro phi psi h
    exact congrArg Subtype.val h
  omega
