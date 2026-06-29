import Mathlib.Tactic
import Tablet.BinarySequenceWeight
import Tablet.StarProductConcreteMarked
import Tablet.StarProductMarkedTupleSignature
import Tablet.StarProductPathRankAtMostSize
import Tablet.StarProductPathUnmarkedBound

-- [TABLET NODE: StarProductConcretePathUnmarkedCertificate]

universe u

theorem StarProductConcretePathUnmarkedCertificate (K : Type u)
    [Field K] (t q k w : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    [Fintype (ProductDigraphVertex (PolarityGraph K t))]
    (ell : ∀ m : ℕ,
      (Fin m → ProductDigraphVertex (PolarityGraph K t)) → ℕ → ℕ)
    (v : Fin k → ProductDigraphVertex (PolarityGraph K t))
    (rho N : ℝ) (psi : ℕ → Fin (t + 1))
    (hrho_nonneg : 0 ≤ rho)
    (hinit : ∀ l, StarProductPathRankAtMostSize K t v l 0 ≤ N)
    (hshrink : ∀ i, i < k →
      (i + 1) ∈
        (Finset.univ.filter
          (fun j : Fin k =>
            StarProductMarkedTupleSignature (PolarityGraph K t)
              (StarProductConcreteMarked K t q ell) v j = true)).image
          (fun j : Fin k => j.1 + 1) →
        StarProductPathRankAtMostSize K t v (psi (i + 1)) (i + 1) ≤
          rho * StarProductPathRankAtMostSize K t v (psi (i + 1)) i)
    (hmono : ∀ l i, i < k →
      ¬ ((i + 1) ∈
          (Finset.univ.filter
            (fun j : Fin k =>
              StarProductMarkedTupleSignature (PolarityGraph K t)
                (StarProductConcreteMarked K t q ell) v j = true)).image
            (fun j : Fin k => j.1 + 1) ∧
        psi (i + 1) = l) →
        StarProductPathRankAtMostSize K t v l (i + 1) ≤
          StarProductPathRankAtMostSize K t v l i)
    (hnonempty : ∀ i, i < k →
      (i + 1) ∈
        (Finset.univ.filter
          (fun j : Fin k =>
            StarProductMarkedTupleSignature (PolarityGraph K t)
              (StarProductConcreteMarked K t q ell) v j = true)).image
          (fun j : Fin k => j.1 + 1) →
        1 ≤ StarProductPathRankAtMostSize K t v (psi (i + 1)) i)
    (hcollapse : ∀ c, w / (t + 1) - 1 ≤ c → N * rho ^ c < 1) :
    BinarySequenceWeight
      (StarProductMarkedTupleSignature (PolarityGraph K t)
        (StarProductConcreteMarked K t q ell) v) ≤ w := by
-- BODY
  classical
  let sig := StarProductMarkedTupleSignature (PolarityGraph K t)
    (StarProductConcreteMarked K t q ell) v
  let Ssig : Finset ℕ :=
    (Finset.univ.filter (fun j : Fin k => sig j = true)).image
      (fun j : Fin k => j.1 + 1)
  let unmarked : ℕ → Prop := fun n => n ∈ Ssig
  have hIcc_filter : (Finset.Icc 1 k).filter unmarked = Ssig := by
    ext n
    constructor
    · intro hn
      exact (Finset.mem_filter.mp hn).2
    · intro hn
      have hn_range : n ∈ Finset.Icc 1 k := by
        rcases Finset.mem_image.mp hn with ⟨j, _hj, rfl⟩
        simp
      exact Finset.mem_filter.mpr ⟨hn_range, hn⟩
  have hSsig_card :
      Ssig.card = (Finset.univ.filter (fun j : Fin k => sig j = true)).card := by
    dsimp [Ssig]
    rw [Finset.card_image_of_injOn]
    intro a _ha b _hb hab
    exact Fin.ext (Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hab))
  have hpath :=
    StarProductPathUnmarkedBound t k w rho N
      (StarProductPathRankAtMostSize K t v)
      unmarked psi hrho_nonneg hinit
      (by
        intro i hi hui
        exact hshrink i hi (by simpa [sig, Ssig, unmarked] using hui))
      (by
        intro l i hi hnot
        exact hmono l i hi (by simpa [sig, Ssig, unmarked] using hnot))
      (by
        intro i hi hui
        exact hnonempty i hi (by simpa [sig, Ssig, unmarked] using hui))
      hcollapse
  unfold BinarySequenceWeight
  rw [← hSsig_card, ← hIcc_filter]
  exact hpath
