import Mathlib.Tactic
import Tablet.ForwardIndependentTuple
import Tablet.StarProductConcreteMarked
import Tablet.StarProductMarkedChildrenBound
import Tablet.StarProductDigraph

-- [TABLET NODE: StarProductConcreteMarkedChildrenCertificate]

universe u

theorem StarProductConcreteMarkedChildrenCertificate (K : Type u)
    [Field K] (t q A h k : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ell : ∀ m : ℕ,
      (Fin m → ProductDigraphVertex (PolarityGraph K t)) → ℕ → ℕ)
    (hpopular : ∀ (m : ℕ), m < k →
      ∀ p : Fin m → ProductDigraphVertex (PolarityGraph K t),
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) p →
          Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
            ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
                (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ∧
              StarProductPopularChild K t q ell p x} ≤ 128 * t * q ^ t)
    (hpoor : ∀ (m : ℕ), m < k →
      ∀ p : Fin m → ProductDigraphVertex (PolarityGraph K t),
        ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) p →
          Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
            ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
                (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ∧
              StarProductPoorChild K t q ell p x} ≤ 10000 * t * q ^ t)
    (hA : 10128 * t ≤ A) (hh : A * q ^ t ≤ h) :
    ∀ (m : ℕ), m < k → ∀ p : Fin m → ProductDigraphVertex (PolarityGraph K t),
      ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t)) p →
        Nat.card {x : ProductDigraphVertex (PolarityGraph K t) //
          ForwardIndependentTuple (StarProductDigraph (PolarityGraph K t))
              (@Fin.snoc m (fun _ => ProductDigraphVertex (PolarityGraph K t)) p x) ∧
            StarProductConcreteMarked K t q ell m p x = true} ≤ h := by
-- BODY
  classical
  intro m hm p hp
  let W := ProductDigraphVertex (PolarityGraph K t)
  let D := StarProductDigraph (PolarityGraph K t)
  let Marked := {x : W //
    ForwardIndependentTuple D
        (@Fin.snoc m (fun _ => W) p x) ∧
      StarProductConcreteMarked K t q ell m p x = true}
  let Popular := {x : W //
    ForwardIndependentTuple D
        (@Fin.snoc m (fun _ => W) p x) ∧
      StarProductPopularChild K t q ell p x}
  let Poor := {x : W //
    ForwardIndependentTuple D
        (@Fin.snoc m (fun _ => W) p x) ∧
      StarProductPoorChild K t q ell p x}
  let encode : Marked → Popular ⊕ Poor := fun x =>
    if hpop : StarProductPopularChild K t q ell p x.1 then
      Sum.inl ⟨x.1, x.2.1, hpop⟩
    else
      have hdisj :
          StarProductPopularChild K t q ell p x.1 ∨
            StarProductPoorChild K t q ell p x.1 := by
        have hxmark := x.2.2
        dsimp [StarProductConcreteMarked] at hxmark
        rw [decide_eq_true_eq] at hxmark
        exact hxmark.2
      Sum.inr ⟨x.1, x.2.1, hdisj.resolve_left hpop⟩
  have hencode_inj : Function.Injective encode := by
    intro x y hxy
    dsimp [encode] at hxy
    split at hxy <;> split at hxy
    · injection hxy with h
      apply Subtype.ext
      exact congrArg (fun z : Popular => (z : W)) h
    · cases hxy
    · cases hxy
    · injection hxy with h
      apply Subtype.ext
      exact congrArg (fun z : Poor => (z : W)) h
  have hcard_encode :
      Nat.card Marked ≤ Nat.card (Popular ⊕ Poor) := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    exact Fintype.card_le_of_injective encode hencode_inj
  have hsum :
      Nat.card Marked ≤ Nat.card Popular + Nat.card Poor := by
    simpa [Nat.card_sum] using hcard_encode
  have hpaper :
      Nat.card Popular + Nat.card Poor ≤ A * q ^ t :=
    StarProductMarkedChildrenBound q t A (Nat.card Popular) (Nat.card Poor)
      (by simpa [Popular, W, D] using hpopular m hm p hp)
      (by simpa [Poor, W, D] using hpoor m hm p hp)
      hA
  exact hsum.trans (hpaper.trans hh)
