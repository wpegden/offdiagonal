import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic
import Tablet.StarProductGeometricSumLeTwoPow
import Tablet.StarProductSubspacePoints

-- [TABLET NODE: StarProductSubspacePointsBound]

universe u

theorem StarProductSubspacePointsBound (K : Type u) [Field K] [Fintype K]
    (t q d : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    {m : ℕ}
    (p : Fin m → ProductDigraphVertex (PolarityGraph K t))
    (y : Projectivization K (Fin (t + 1) → K))
    (hq : q = Fintype.card K)
    (hdim : Module.finrank K (StarProductPrefixSpan K t p y) = d) :
    ((StarProductSubspacePoints K t p y).card : ℝ) ≤
      2 * (q : ℝ) ^ d / (q : ℝ) := by
-- BODY
  classical
  let W := StarProductPrefixSpan K t p y
  let S := StarProductSubspacePoints K t p y
  letI : Fintype W := Fintype.ofFinite _
  letI : Fintype (Projectivization K W) := Fintype.ofFinite _
  let lift : S → Projectivization K W := fun b =>
    Projectivization.mk K
      (⟨Projectivization.rep b.1, by
        have hb := b.2
        simpa [S, StarProductSubspacePoints, W] using (Finset.mem_filter.mp hb).2⟩ : W)
      (by
        intro hzero
        exact Projectivization.rep_nonzero b.1 (Subtype.ext_iff.mp hzero))
  have hlift : ∀ b : S,
      Projectivization.map W.subtype W.injective_subtype (lift b) = b.1 := by
    intro b
    dsimp [lift]
    rw [Projectivization.map_mk]
    change Projectivization.mk K (Projectivization.rep b.1) _ = b.1
    exact Projectivization.mk_rep b.1
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    calc
      a.1 = Projectivization.map W.subtype W.injective_subtype (lift a) := (hlift a).symm
      _ = Projectivization.map W.subtype W.injective_subtype (lift b) := by rw [hab]
      _ = b.1 := hlift b
  have hcardS : S.card ≤ Fintype.card (Projectivization K W) := by
    simpa using Fintype.card_le_of_injective lift hinj
  have hproj : Fintype.card (Projectivization K W) =
      ∑ i ∈ Finset.range d, q ^ i := by
    rw [← Nat.card_eq_fintype_card]
    rw [Projectivization.card_of_finrank K W (by simpa [W] using hdim)]
    simp [Nat.card_eq_fintype_card, hq]
  have hcardR :
      ((S.card : ℝ) ≤ ((∑ i ∈ Finset.range d, q ^ i : ℕ) : ℝ)) := by
    exact_mod_cast (hcardS.trans (le_of_eq hproj))
  have hgeomR :
      ((∑ i ∈ Finset.range d, q ^ i : ℕ) : ℝ) ≤
        2 * (q : ℝ) ^ d / (q : ℝ) := by
    have hqpos : 0 < q := by
      rw [hq]
      exact Fintype.card_pos
    have hqne : (q : ℝ) ≠ 0 := by exact_mod_cast hqpos.ne'
    cases d with
    | zero =>
        have hqposR : 0 < (q : ℝ) := by exact_mod_cast hqpos
        simpa using div_nonneg (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hqposR)
    | succ n =>
        have hsumnat := StarProductGeometricSumLeTwoPow K q n hq
        have hsumR :
            ((∑ i ∈ Finset.range (n + 1), q ^ i : ℕ) : ℝ) ≤
              (2 * q ^ n : ℕ) := by
          exact_mod_cast hsumnat
        refine hsumR.trans_eq ?_
        field_simp [hqne]
        rw [pow_succ]
        norm_num [Nat.cast_mul, Nat.cast_pow]
        ring
  exact hcardR.trans hgeomR
