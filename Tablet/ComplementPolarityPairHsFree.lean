import Tablet.HsFreePair
import Tablet.LoopGraphComplement
import Tablet.PolarityGraphSkewFree

-- [TABLET NODE: ComplementPolarityPairHsFree]

universe u

theorem ComplementPolarityPairHsFree (K : Type u) [Field K] (s : ℕ) (hs : 2 ≤ s) :
    HsFreePair (LoopGraphComplement (PolarityGraph K (s - 2)))
      (PolarityGraph K (s - 2)) s := by
-- BODY
  sorry
