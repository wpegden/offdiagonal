import Tablet.Digraph

-- [TABLET NODE: TransitiveTournamentFree]

universe u

def TransitiveTournamentFree {V : Type u} (D : Digraph V) (s : ℕ) : Prop :=
-- BODY
  ¬ ∃ v : Fin s → V,
      Function.Injective v ∧ ∀ i j : Fin s, i < j → D (v i) (v j)
