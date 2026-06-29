import Tablet.ForwardIndependentTupleCount
import Tablet.MarkedTreePathCounting
import Tablet.StarProductMarkedTupleFiberBound

-- [TABLET NODE: StarProductMarkedTreeCountingBridge]

universe u

theorem StarProductMarkedTreeCountingBridge {V : Type u}
    (G : LoopGraph V) [Fintype (ProductDigraphVertex G)]
    (k w Delta h : ℕ)
    (marked : ∀ m : ℕ, (Fin m → ProductDigraphVertex G) → ProductDigraphVertex G → Bool)
    (hk : w ≤ k) (hhDelta : h ≤ Delta)
    (hpath : ∀ v : Fin k → ProductDigraphVertex G,
      ForwardIndependentTuple (StarProductDigraph G) v →
        BinarySequenceWeight (StarProductMarkedTupleSignature G marked v) ≤ w)
    (hAll : ∀ (m : ℕ), m < k → ∀ p : Fin m → ProductDigraphVertex G,
      ForwardIndependentTuple (StarProductDigraph G) p →
        Nat.card {x : ProductDigraphVertex G //
          ForwardIndependentTuple (StarProductDigraph G)
            (@Fin.snoc m (fun _ => ProductDigraphVertex G) p x)} ≤ Delta)
    (hMarked : ∀ (m : ℕ), m < k → ∀ p : Fin m → ProductDigraphVertex G,
      ForwardIndependentTuple (StarProductDigraph G) p →
        Nat.card {x : ProductDigraphVertex G //
          ForwardIndependentTuple (StarProductDigraph G)
              (@Fin.snoc m (fun _ => ProductDigraphVertex G) p x) ∧
            marked m p x = true} ≤ h) :
    ForwardIndependentTupleCount (StarProductDigraph G) k ≤
      2 ^ k * Delta ^ w * h ^ (k - w) := by
-- BODY
  classical
  let P := {v : Fin k → ProductDigraphVertex G //
    ForwardIndependentTuple (StarProductDigraph G) v}
  let signature : P → Fin k → Bool := fun p =>
    StarProductMarkedTupleSignature G marked p.1
  have hpath' : ∀ p : P, BinarySequenceWeight (signature p) ≤ w := by
    intro p
    exact hpath p.1 p.2
  have hfiber : ∀ z : Fin k → Bool,
      Fintype.card {p : P // signature p = z} ≤
        Delta ^ BinarySequenceWeight z * h ^ (k - BinarySequenceWeight z) := by
    intro z
    simpa [StarProductMarkedTupleFiberCount, P, signature] using
      StarProductMarkedTupleFiberBound G k Delta h marked hAll hMarked z
  have hcount :=
    MarkedTreePathCounting k w Delta h signature hk hhDelta hpath' hfiber
  simpa [ForwardIndependentTupleCount, P] using hcount
