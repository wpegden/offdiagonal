import Mathlib.FieldTheory.Finiteness
import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTuplePrefixSpanCard]

theorem F2BadTuplePrefixSpanCard (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2)) (i : ℕ) :
    Nat.card
        (Submodule.span (ZMod 2)
          (Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1))) =
      2 ^ F2BadTupleRank p k ab i := by
-- BODY
  classical
  let S : Submodule (ZMod 2) (Fin p → ZMod 2) :=
    Submodule.span (ZMod 2)
      (Set.range (fun j : {j : Fin k // j.val < i} => (ab j.1).1))
  change Nat.card S = 2 ^ F2BadTupleRank p k ab i
  haveI : Fintype S := Fintype.ofFinite S
  rw [Nat.card_eq_fintype_card]
  rw [Module.card_eq_pow_finrank (K := ZMod 2) (V := S)]
  norm_num [ZMod.card, F2BadTupleRank, S]
