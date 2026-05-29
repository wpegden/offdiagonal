import Tablet.HsFreePair
import Tablet.LoopGraphComplement
import Tablet.PolarityGraphSkewFree

-- [TABLET NODE: ComplementPolarityPairHsFree]

universe u

theorem ComplementPolarityPairHsFree (K : Type u) [Field K] (s : ℕ) (hs : 2 ≤ s) :
    HsFreePair (LoopGraphComplement (PolarityGraph K (s - 2)))
      (PolarityGraph K (s - 2)) s := by
-- BODY
  rw [HsFreePair]
  intro h
  rcases h with ⟨a, b, hdiag, hoff⟩
  have hskew : NoSkewBipartiteConfiguration (PolarityGraph K (s - 2)) s := by
    simpa [Nat.sub_add_cancel hs] using PolarityGraphSkewFree K (s - 2)
  exact hskew ⟨a, b, hoff, hdiag⟩
