import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Tablet.F2BadTupleRank

-- [TABLET NODE: F2BadTupleRankOne]

theorem F2BadTupleRankOne (p k : ℕ)
    (ab : Fin k → (Fin p → ZMod 2) × (Fin p → ZMod 2))
    (hbad : F2BadTuple p k ab) (hk : 0 < k) :
    F2BadTupleRank p k ab 1 = 1 := by
-- BODY
  classical
  let i0 : Fin k := ⟨0, hk⟩
  have hrange :
      Set.range (fun j : {j : Fin k // j.val < 1} => (ab j.1).1) =
        {(ab i0).1} := by
    ext v
    constructor
    · rintro ⟨j, rfl⟩
      have hj : j.1 = i0 := by
        apply Fin.ext
        have hj0 : j.1.val = 0 := by omega
        simpa [i0] using hj0
      simp [hj]
    · intro hv
      have hv' : v = (ab i0).1 := by simpa using hv
      subst v
      refine ⟨⟨i0, by simp [i0]⟩, rfl⟩
  have hnonzero : (ab i0).1 ≠ 0 := by
    intro hzero
    have hdot : (ab i0).1 ⬝ᵥ (ab i0).2 = 1 := hbad i0 i0 le_rfl
    rw [hzero] at hdot
    simp [dotProduct] at hdot
  dsimp [F2BadTupleRank]
  rw [hrange]
  exact finrank_span_singleton hnonzero
