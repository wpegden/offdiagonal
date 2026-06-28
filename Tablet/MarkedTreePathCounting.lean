import Tablet.BinarySequenceWeight

-- [TABLET NODE: MarkedTreePathCounting]

universe u

theorem MarkedTreePathCounting {P : Type u} [Fintype P]
    (k w Delta h : ℕ) (signature : P → Fin k → Bool)
    (hk : w ≤ k) (hhDelta : h ≤ Delta)
    (hpath : ∀ p : P, BinarySequenceWeight (signature p) ≤ w)
    (hfiber : ∀ z : Fin k → Bool,
      Fintype.card {p : P // signature p = z} ≤
        Delta ^ BinarySequenceWeight z * h ^ (k - BinarySequenceWeight z)) :
    Fintype.card P ≤ 2 ^ k * Delta ^ w * h ^ (k - w) := by
-- BODY
  classical
  let Fiber (z : Fin k → Bool) := {p : P // signature p = z}
  let e : P ≃ Sigma Fiber := {
    toFun := fun p => ⟨signature p, ⟨p, rfl⟩⟩
    invFun := fun q => q.2.1
    left_inv := fun p => rfl
    right_inv := fun q => by
      cases q with
      | mk z q =>
        cases q with
        | mk p hp =>
          cases hp
          rfl
  }
  have hcard_sum :
      Fintype.card P = ∑ z : Fin k → Bool, Fintype.card (Fiber z) := by
    calc
      Fintype.card P = Fintype.card (Sigma Fiber) := Fintype.card_congr e
      _ = ∑ z : Fin k → Bool, Fintype.card (Fiber z) := Fintype.card_sigma
  have hmono {m : ℕ} (hmw : m ≤ w) :
      Delta ^ m * h ^ (k - m) ≤ Delta ^ w * h ^ (k - w) := by
    have hdecomp : k - m = (w - m) + (k - w) := by omega
    have hpow : h ^ (w - m) ≤ Delta ^ (w - m) := by
      exact pow_le_pow_left₀ (Nat.zero_le h) hhDelta (w - m)
    calc
      Delta ^ m * h ^ (k - m)
          = Delta ^ m * (h ^ (w - m) * h ^ (k - w)) := by
              rw [hdecomp, pow_add]
      _ ≤ Delta ^ m * (Delta ^ (w - m) * h ^ (k - w)) := by
              exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hpow)
      _ = Delta ^ w * h ^ (k - w) := by
              have hadd : m + (w - m) = w := Nat.add_sub_of_le hmw
              rw [← Nat.mul_assoc, ← pow_add, hadd]
  have hfiber_uniform :
      ∀ z : Fin k → Bool, Fintype.card (Fiber z) ≤ Delta ^ w * h ^ (k - w) := by
    intro z
    by_cases hnonempty : Nonempty (Fiber z)
    · rcases hnonempty with ⟨p⟩
      have hz_weight : BinarySequenceWeight z ≤ w := by
        simpa [p.2] using hpath p.1
      exact (hfiber z).trans (hmono hz_weight)
    · have hempty : Fintype.card (Fiber z) = 0 := by
        exact Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hnonempty)
      rw [hempty]
      exact Nat.zero_le _
  calc
    Fintype.card P
        = ∑ z : Fin k → Bool, Fintype.card (Fiber z) := hcard_sum
    _ ≤ ∑ z : Fin k → Bool, Delta ^ w * h ^ (k - w) := by
        exact Finset.sum_le_sum (fun z _ => hfiber_uniform z)
    _ = Fintype.card (Fin k → Bool) * (Delta ^ w * h ^ (k - w)) := by
        simp [Finset.sum_const]
    _ = 2 ^ k * Delta ^ w * h ^ (k - w) := by
        rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
        ring
