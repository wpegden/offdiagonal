import Tablet.ComplementPolarityPairHsFree
import Tablet.LoopGraphComplementNdLambda
import Tablet.PolarityGraphParameters

-- [TABLET NODE: MainTheoremPolaritySetup]

universe u

theorem MainTheoremPolaritySetup (K : Type u) [Field K] [Fintype K]
    (s q : ℕ)
    [Fintype (Projectivization K (Fin ((s - 2) + 1) → K))]
    (hs : 4 ≤ s) (hq : q = Fintype.card K) :
    let t := s - 2
    let n := (q ^ (t + 1) - 1) / (q - 1)
    let dG := (q ^ t - 1) / (q - 1)
    let dF := n - dG
    let lambda :=
      Real.sqrt ((((q ^ t - 1) / (q - 1)) -
        ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ)
    LoopGraphNdLambda (PolarityGraph K t) n dG lambda ∧
      LoopGraphNdLambda (LoopGraphComplement (PolarityGraph K t)) n dF lambda ∧
        HsFreePair (LoopGraphComplement (PolarityGraph K t))
          (PolarityGraph K t) s := by
-- BODY
  dsimp
  have ht : 2 ≤ s - 2 := by omega
  have hs_two : 2 ≤ s := by omega
  have hG := PolarityGraphParameters K (s - 2) q ht hq
  exact ⟨hG, LoopGraphComplementNdLambda (PolarityGraph K (s - 2)) _ _ _ hG,
    ComplementPolarityPairHsFree K s hs_two⟩
