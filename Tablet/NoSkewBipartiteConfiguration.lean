import Tablet.LoopGraph

-- [TABLET NODE: NoSkewBipartiteConfiguration]

universe u

def NoSkewBipartiteConfiguration {V : Type u} (G : LoopGraph V) (s : ℕ) : Prop :=
-- BODY
  ¬ ∃ a b : Fin s → V,
      (∀ i j : Fin s, i < j → G (a i) (b j)) ∧
        ∀ i : Fin s, ¬ G (a i) (b i)
