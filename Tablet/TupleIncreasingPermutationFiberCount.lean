import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Fin.Basic
import Tablet.Preamble

-- [TABLET NODE: TupleIncreasingPermutationFiberCount]

universe u

theorem TupleIncreasingPermutationFiberCount {W : Type u} [Fintype W]
    {k : ℕ} (v : Fin k → W) (r : W → ℕ)
    (hv : Function.Injective v) (hr : Set.InjOn r (Set.range v)) :
    Nat.factorial k *
        Fintype.card {σ : Equiv.Perm (Fin k) //
          StrictMono (fun i : Fin k => r (v (σ i)))} =
      Fintype.card (Equiv.Perm (Fin k)) := by
-- BODY
  classical
  let f : Fin k → ℕ := fun i => r (v i)
  have hf_inj : Function.Injective f := by
    intro i j hij
    apply hv
    apply hr
    · exact ⟨i, rfl⟩
    · exact ⟨j, rfl⟩
    · exact hij
  have hsub :
      Subsingleton {σ : Equiv.Perm (Fin k) //
        StrictMono (fun i : Fin k => r (v (σ i)))} := by
    refine ⟨?_⟩
    intro a b
    apply Subtype.ext
    have hrange_a :
        Set.range (fun i : Fin k => f (a.1 i)) = Set.range f := by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨a.1 i, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨a.1.symm i, ?_⟩
        simp [f]
    have hrange_b :
        Set.range (fun i : Fin k => f (b.1 i)) = Set.range f := by
      apply Set.ext
      intro x
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨b.1 i, rfl⟩
      · rintro ⟨i, rfl⟩
        refine ⟨b.1.symm i, ?_⟩
        simp [f]
    have ha : StrictMono (fun i : Fin k => f (a.1 i)) := by
      simpa [f] using a.2
    have hb : StrictMono (fun i : Fin k => f (b.1 i)) := by
      simpa [f] using b.2
    have hcomp :
        (fun i : Fin k => f (a.1 i)) =
          fun i : Fin k => f (b.1 i) := by
      exact (StrictMono.range_inj ha hb).mp (by rw [hrange_a, hrange_b])
    apply Equiv.ext
    intro i
    exact hf_inj (congrFun hcomp i)
  have hnon :
      Nonempty {σ : Equiv.Perm (Fin k) //
        StrictMono (fun i : Fin k => r (v (σ i)))} := by
    let R : Finset ℕ := Finset.univ.image f
    have hfinjOn : Set.InjOn f (↑(Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
      intro i _ j _ hij
      exact hf_inj hij
    have hRcard : R.card = k := by
      simpa [R] using
        (Finset.card_image_of_injOn
          (s := (Finset.univ : Finset (Fin k))) hfinjOn)
    let rank : Fin k → ℕ := R.orderEmbOfFin hRcard
    have hrank_mem : ∀ i : Fin k, rank i ∈ R := by
      intro i
      dsimp [rank]
      exact Finset.orderEmbOfFin_mem R hRcard i
    have hpre : ∀ i : Fin k, ∃ j : Fin k, f j = rank i := by
      intro i
      have hi : rank i ∈ Finset.univ.image f := by
        simpa [R] using hrank_mem i
      rcases Finset.mem_image.mp hi with ⟨j, _hj, hfj⟩
      exact ⟨j, hfj⟩
    let sort : Fin k → Fin k := fun i => Classical.choose (hpre i)
    have hsort_rank : ∀ i : Fin k, f (sort i) = rank i := by
      intro i
      exact Classical.choose_spec (hpre i)
    have hsort_inj : Function.Injective sort := by
      intro i j hij
      apply (R.orderEmbOfFin hRcard).injective
      calc
        rank i = f (sort i) := (hsort_rank i).symm
        _ = f (sort j) := by rw [hij]
        _ = rank j := hsort_rank j
    have hsort_surj : Function.Surjective sort :=
      (Finite.injective_iff_surjective).mp hsort_inj
    let sortPerm : Equiv.Perm (Fin k) :=
      Equiv.ofBijective sort ⟨hsort_inj, hsort_surj⟩
    refine ⟨⟨sortPerm, ?_⟩⟩
    intro i j hij
    have hrank_lt : rank i < rank j :=
      (R.orderEmbOfFin hRcard).strictMono hij
    simpa [sortPerm, sort, f, hsort_rank] using hrank_lt
  letI : Unique {σ : Equiv.Perm (Fin k) //
      StrictMono (fun i : Fin k => r (v (σ i)))} :=
    { default := Classical.choice hnon
      uniq := fun a => Subsingleton.elim a (Classical.choice hnon) }
  rw [Fintype.card_unique, Fintype.card_perm, Fintype.card_fin]
  simp
