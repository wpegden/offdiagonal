import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.Tactic
import Tablet.Preamble

-- [TABLET NODE: StarProductFixedBExtensionBound]

universe u

theorem StarProductFixedBExtensionBound (K : Type u) [Field K] [Fintype K]
    (t q r : ℕ)
    (Wperp : Submodule K (Fin (t + 1) → K))
    [Fintype Wperp] [Fintype (Projectivization K Wperp)]
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    (hq : q = Fintype.card K)
    (hdim : Module.finrank K Wperp = t + 1 - r)
    (hgeom : (∑ i ∈ Finset.range (t + 1 - r), q ^ i) ≤ 2 * q ^ (t - r))
    (Ext : Finset (Projectivization K (Fin (t + 1) → K)))
    (hExt : ∀ a ∈ Ext, ∃ x : Projectivization K Wperp,
      Projectivization.map Wperp.subtype Wperp.injective_subtype x = a) :
    Ext.card ≤ 2 * q ^ (t - r) := by
-- BODY
  classical
  let lift : Ext → Projectivization K Wperp := fun a => Classical.choose (hExt a.1 a.2)
  have hlift : ∀ a : Ext,
      Projectivization.map Wperp.subtype Wperp.injective_subtype (lift a) = a.1 := by
    intro a
    exact Classical.choose_spec (hExt a.1 a.2)
  have hinj : Function.Injective lift := by
    intro a b hab
    apply Subtype.ext
    calc
      a.1 = Projectivization.map Wperp.subtype Wperp.injective_subtype (lift a) := (hlift a).symm
      _ = Projectivization.map Wperp.subtype Wperp.injective_subtype (lift b) := by rw [hab]
      _ = b.1 := hlift b
  have hcardExt : Ext.card ≤ Fintype.card (Projectivization K Wperp) := by
    simpa using Fintype.card_le_of_injective lift hinj
  have hproj : Fintype.card (Projectivization K Wperp) =
      ∑ i ∈ Finset.range (t + 1 - r), q ^ i := by
    rw [← Nat.card_eq_fintype_card]
    rw [Projectivization.card_of_finrank K Wperp hdim]
    simp [Nat.card_eq_fintype_card, hq]
  exact hcardExt.trans (by simpa [hproj] using hgeom)
