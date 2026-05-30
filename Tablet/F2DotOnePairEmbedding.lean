import Mathlib.Data.Fintype.EquivFin
import Tablet.F2DotOnePairCard

-- [TABLET NODE: F2DotOnePairEmbedding]

theorem F2DotOnePairEmbedding (s : ℕ) (hs : 4 ≤ s) :
    Nonempty
      (Fin (2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1) ↪
        {z : ((Fin (s - 1) → ZMod 2) × (Fin (s - 1) → ZMod 2)) //
          z.1 ⬝ᵥ z.2 = 1}) := by
-- BODY
  classical
  let N : ℕ := 2 ^ (2 * s - 3) - 2 ^ (s - 1) - 2 ^ (s - 2) + 1
  let U : Type := {z : ((Fin (s - 1) → ZMod 2) × (Fin (s - 1) → ZMod 2)) //
          z.1 ⬝ᵥ z.2 = 1}
  have hcardU :
      Fintype.card U = (2 ^ (s - 1) - 1) * 2 ^ (s - 2) := by
    dsimp [U]
    simpa using F2DotOnePairCard (s - 1)
  have hpow : 2 ^ (2 * s - 3) = 2 ^ (s - 1) * 2 ^ (s - 2) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  have hle : N ≤ Fintype.card U := by
    dsimp [N]
    rw [hcardU, hpow]
    set A : ℕ := 2 ^ (s - 1)
    set B : ℕ := 2 ^ (s - 2)
    have hA : 2 ≤ A := by
      dsimp [A]
      simpa using
        (Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) (by omega : 1 ≤ s - 1))
    have hB : 2 ≤ B := by
      dsimp [B]
      simpa using
        (Nat.pow_le_pow_right (n := 2) (by norm_num : 0 < 2) (by omega : 1 ≤ s - 2))
    have hsum : A + B ≤ A * B := by nlinarith
    rw [Nat.sub_mul, one_mul]
    change A * B - A - B + 1 ≤ A * B - B
    rw [Nat.sub_sub]
    omega
  have hle' : Fintype.card (Fin N) ≤ Fintype.card U := by
    simpa [Fintype.card_fin] using hle
  simpa [N, U] using
    (Function.Embedding.nonempty_of_card_le (α := Fin N) (β := U) hle')
