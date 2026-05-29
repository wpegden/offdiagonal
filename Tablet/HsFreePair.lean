import Tablet.LoopGraph

-- [TABLET NODE: HsFreePair]

universe u

def HsFreePair {V : Type u} (F G : LoopGraph V) (s : ℕ) : Prop :=
-- BODY
  ¬ ∃ a b : Fin s → V,
      (∀ i : Fin s, F (a i) (b i)) ∧
        ∀ i j : Fin s, i < j → G (a i) (b j)
