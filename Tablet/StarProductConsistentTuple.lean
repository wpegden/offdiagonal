import Tablet.LoopGraph

-- [TABLET NODE: StarProductConsistentTuple]

universe u

def StarProductConsistentTuple {V : Type u} (G : LoopGraph V) {m : ℕ}
    (a b : Fin m → V) : Prop :=
-- BODY
  (∀ i : Fin m, G (a i) (b i)) ∧
    ∀ i j : Fin m, i < j → G (a i) (b j) → G (a j) (b i)
