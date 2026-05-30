import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Tablet.LoopGraphNdLambda
import Tablet.PolarityGraph

-- [TABLET NODE: PolarityGraphParameters]

universe u

theorem PolarityGraphParameters (K : Type u) [Field K] [Fintype K] (t q : ℕ)
    [Fintype (Projectivization K (Fin (t + 1) → K))]
    (ht : 2 ≤ t) (hq : q = Fintype.card K) :
    LoopGraphNdLambda (PolarityGraph K t)
      ((q ^ (t + 1) - 1) / (q - 1))
      ((q ^ t - 1) / (q - 1))
      (Real.sqrt
        ((((q ^ t - 1) / (q - 1)) -
          ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ)) := by
-- BODY
  dsimp [LoopGraphNdLambda]
  have hdegree :
      ∀ v : Projectivization K (Fin (t + 1) → K),
        LoopGraphDegree (PolarityGraph K t) v = ((q ^ t - 1) / (q - 1)) := by
    classical
    intro v
    induction v using Projectivization.ind with
    | h x hx =>
      dsimp [LoopGraphDegree, PolarityGraph]
      have hsub :
          ({ w : Projectivization K (Fin (t + 1) → K) |
            Projectivization.orthogonal (Projectivization.mk K x hx) w } :
              Finset (Projectivization K (Fin (t + 1) → K))).card =
            Fintype.card
              { w : Projectivization K (Fin (t + 1) → K) //
                Projectivization.orthogonal (Projectivization.mk K x hx) w } := by
        simpa using (Fintype.card_subtype
          (fun w : Projectivization K (Fin (t + 1) → K) =>
            Projectivization.orthogonal (Projectivization.mk K x hx) w)).symm
      refine hsub.trans ?_
      change Fintype.card
          { w : Projectivization K (Fin (t + 1) → K) //
            Projectivization.orthogonal (Projectivization.mk K x hx) w } =
        ((q ^ t - 1) / (q - 1))
      obtain ⟨i, hxi⟩ : ∃ i, x i ≠ 0 := by
        simpa [funext_iff] using hx
      let φ : (Fin (t + 1) → K) →ₗ[K] K :=
        { toFun := fun y => x ⬝ᵥ y
          map_add' := by
            intro y z
            exact dotProduct_add x y z
          map_smul' := by
            intro a y
            exact dotProduct_smul a x y }
      have hφ_eval : φ (Pi.single i (1 : K)) = x i := by
        change x ⬝ᵥ Pi.single i (1 : K) = x i
        rw [dotProduct, Finset.sum_eq_single i]
        · simp
        · intro j _ hji
          simp [Pi.single_eq_of_ne hji]
        · intro hi
          simp at hi
      have hφ_nonzero : φ ≠ 0 := by
        intro hφ
        have hval := congr_fun
          (show (φ : (Fin (t + 1) → K) → K) = 0 from congrArg DFunLike.coe hφ)
          (Pi.single i (1 : K))
        rw [hφ_eval] at hval
        exact hxi hval
      have hφ_surj : Function.Surjective φ := by
        intro a
        refine ⟨(a / x i) • (Pi.single i (1 : K) : Fin (t + 1) → K), ?_⟩
        rw [map_smul, hφ_eval]
        change (a / x i) * x i = a
        field_simp [hxi]
      have hφ_range : φ.range = ⊤ := LinearMap.range_eq_top.mpr hφ_surj
      let ι : φ.ker →ₗ[K] (Fin (t + 1) → K) := φ.ker.subtype
      have hι_inj : Function.Injective ι := φ.ker.injective_subtype
      let ψ : Projectivization K φ.ker → Projectivization K (Fin (t + 1) → K) :=
        Projectivization.map ι hι_inj
      have hψ_inj : Function.Injective ψ := Projectivization.map_injective ι hι_inj
      have hψ_range :
          Set.range ψ =
            { w : Projectivization K (Fin (t + 1) → K) |
              Projectivization.orthogonal (Projectivization.mk K x hx) w } := by
        ext w
        constructor
        · rintro ⟨z, rfl⟩
          induction z using Projectivization.ind with
          | h y hy =>
            change Projectivization.orthogonal (Projectivization.mk K x hx)
              (Projectivization.map ι hι_inj (Projectivization.mk K y hy))
            rw [Projectivization.map_mk]
            rw [Projectivization.orthogonal_mk hx]
            change x ⬝ᵥ (y : Fin (t + 1) → K) = 0
            exact y.property
        · intro hw
          induction w using Projectivization.ind with
          | h y hy =>
            have hyker : y ∈ φ.ker := by
              change φ y = 0
              change x ⬝ᵥ y = 0
              exact (Projectivization.orthogonal_mk hx hy).mp hw
            refine ⟨Projectivization.mk K (⟨y, hyker⟩ : φ.ker) ?_, ?_⟩
            · intro hzero
              exact hy (congrArg Subtype.val hzero)
            · change Projectivization.map ι hι_inj
                  (Projectivization.mk K (⟨y, hyker⟩ : φ.ker) ?_) =
                Projectivization.mk K y hy
              rw [Projectivization.map_mk]
              rfl
      haveI : Fintype φ.ker := Fintype.ofFinite φ.ker
      haveI : Fintype (Projectivization K φ.ker) :=
        Fintype.ofFinite (Projectivization K φ.ker)
      have horth_card :
          Fintype.card
              { w : Projectivization K (Fin (t + 1) → K) //
                Projectivization.orthogonal (Projectivization.mk K x hx) w } =
            Fintype.card (Projectivization K φ.ker) := by
        let eRange : Projectivization K φ.ker ≃ Set.range ψ :=
          Equiv.ofInjective ψ hψ_inj
        let eSet : Set.range ψ ≃
            { w : Projectivization K (Fin (t + 1) → K) //
              Projectivization.orthogonal (Projectivization.mk K x hx) w } :=
          Equiv.setCongr hψ_range
        exact (Fintype.card_congr (eRange.trans eSet)).symm
      let drop : φ.ker → ({ j : Fin (t + 1) // j ≠ i } → K) := fun y j => y.1 j.1
      let extend : ({ j : Fin (t + 1) // j ≠ i } → K) → φ.ker := fun z =>
        ⟨fun j => if hji : j = i then
            -((∑ k : { j : Fin (t + 1) // j ≠ i }, x k.1 * z k) / x i)
          else z ⟨j, hji⟩,
          by
            change x ⬝ᵥ (fun j => if hji : j = i then
                -((∑ k : { j : Fin (t + 1) // j ≠ i }, x k.1 * z k) / x i)
              else z ⟨j, hji⟩) = 0
            rw [dotProduct, Fintype.sum_eq_add_sum_subtype_ne
              (fun j => x j * (if hji : j = i then
                -((∑ k : { j : Fin (t + 1) // j ≠ i }, x k.1 * z k) / x i)
              else z ⟨j, hji⟩)) i]
            simp [(fun k : { j : Fin (t + 1) // j ≠ i } => k.property)]
            field_simp [hxi]
            ring⟩
      let eKer : φ.ker ≃ ({ j : Fin (t + 1) // j ≠ i } → K) :=
      {
        toFun := drop
        invFun := extend
        left_inv := by
          intro y
          ext j
          by_cases hji : j = i
          · subst j
            dsimp [drop, extend]
            simp
            have hdot : x ⬝ᵥ (y : Fin (t + 1) → K) = 0 := y.property
            rw [dotProduct, Fintype.sum_eq_add_sum_subtype_ne
              (fun j => x j * (y : Fin (t + 1) → K) j) i] at hdot
            let S := ∑ k : { j : Fin (t + 1) // j ≠ i },
              x k.1 * (y : Fin (t + 1) → K) k.1
            have hmul : x i * (y : Fin (t + 1) → K) i = -S := by
              rw [eq_neg_iff_add_eq_zero]
              exact hdot
            field_simp [hxi]
            rw [← hmul]
          · dsimp [drop, extend]
            simp [hji]
        right_inv := by
          intro z
          funext j
          dsimp [drop, extend]
          simp [j.property]
      }
      have hcompl_card : Fintype.card { j : Fin (t + 1) // j ≠ i } = t := by
        rw [Fintype.card_subtype_compl (fun j : Fin (t + 1) => j = i)]
        simp
      have hker_card : Fintype.card φ.ker = q ^ t := by
        calc
          Fintype.card φ.ker = Fintype.card ({ j : Fin (t + 1) // j ≠ i } → K) :=
            Fintype.card_congr eKer
          _ = Fintype.card K ^ Fintype.card { j : Fin (t + 1) // j ≠ i } := by
            rw [Fintype.card_fun]
          _ = q ^ t := by
            rw [hcompl_card, ← hq]
      rw [horth_card]
      rw [← Nat.card_eq_fintype_card]
      rw [Projectivization.card'']
      rw [Nat.card_eq_fintype_card (α := φ.ker), hker_card]
      rw [Nat.card_eq_fintype_card (α := K), ← hq]
  constructor
  · rw [← Nat.card_eq_fintype_card]
    rw [Projectivization.card'']
    rw [Nat.card_eq_fintype_card (α := Fin (t + 1) → K),
      Nat.card_eq_fintype_card (α := K), Fintype.card_fun, Fintype.card_fin]
    rw [← hq]
  constructor
  · dsimp [LoopGraphSymmetric, PolarityGraph]
    intro x y hxy
    exact Projectivization.orthogonal_comm.mp hxy
  constructor
  · exact hdegree
  constructor
  · classical
    intro mu hmu
    dsimp [LoopGraphNonprincipalEigenvalue] at hmu
    rcases hmu with ⟨f, ⟨v0, hv0⟩, hzero, heig⟩
    have hA2_eig :
        LoopGraphAdjacencyAction (PolarityGraph K t)
            (fun v => LoopGraphAdjacencyAction (PolarityGraph K t) f v) v0 =
          mu ^ 2 * f v0 := by
      calc
        LoopGraphAdjacencyAction (PolarityGraph K t)
            (fun v => LoopGraphAdjacencyAction (PolarityGraph K t) f v) v0 =
            LoopGraphAdjacencyAction (PolarityGraph K t) (fun v => mu * f v) v0 := by
          congr
          ext v
          exact heig v
        _ = mu * LoopGraphAdjacencyAction (PolarityGraph K t) f v0 := by
          dsimp [LoopGraphAdjacencyAction]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          by_cases h : PolarityGraph K t v0 w
          · simp [h]
          · simp [h]
        _ = mu * (mu * f v0) := by
          rw [heig v0]
        _ = mu ^ 2 * f v0 := by
          ring
    have hA2_common :
        LoopGraphAdjacencyAction (PolarityGraph K t)
            (fun v => LoopGraphAdjacencyAction (PolarityGraph K t) f v) v0 =
          Finset.univ.sum
            (fun u =>
              (((Finset.univ.filter
                (fun w => PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).card : ℕ) : ℝ) *
                f u) := by
      dsimp [LoopGraphAdjacencyAction]
      calc
        (∑ w, if PolarityGraph K t v0 w then
            (∑ u, if PolarityGraph K t w u then f u else 0) else 0) =
            ∑ w, ∑ u,
              if PolarityGraph K t v0 w ∧ PolarityGraph K t w u then f u else 0 := by
          apply Finset.sum_congr rfl
          intro w _
          by_cases hvw : PolarityGraph K t v0 w
          · simp [hvw]
          · simp [hvw]
        _ = ∑ u, ∑ w,
              if PolarityGraph K t v0 w ∧ PolarityGraph K t w u then f u else 0 := by
          rw [Finset.sum_comm]
        _ = ∑ u,
            (((Finset.univ.filter
              (fun w => PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).card : ℕ) : ℝ) *
              f u := by
          apply Finset.sum_congr rfl
          intro u _
          rw [← Finset.sum_filter]
          simp [Finset.sum_const]
    have hcommon_sum_zero
        (d a : ℕ) (had : a ≤ d) :
        Finset.univ.sum
            (fun u : Projectivization K (Fin (t + 1) → K) =>
              ((if u = v0 then d else a : ℕ) : ℝ) * f u) =
          (((d - a : ℕ) : ℝ) * f v0) := by
      rw [Fintype.sum_eq_add_sum_subtype_ne
        (fun u : Projectivization K (Fin (t + 1) → K) =>
          ((if u = v0 then d else a : ℕ) : ℝ) * f u) v0]
      simp [(fun x : { x : Projectivization K (Fin (t + 1) → K) // x ≠ v0 } =>
        x.property)]
      rw [← Finset.mul_sum]
      have hrest : (∑ u : { x : Projectivization K (Fin (t + 1) → K) // x ≠ v0 },
          f u.1) = -f v0 := by
        have hsum := hzero
        rw [Fintype.sum_eq_add_sum_subtype_ne f v0] at hsum
        linarith
      rw [hrest]
      norm_num
      rw [← sub_eq_add_neg]
      rw [← sub_mul]
      have hcast : ((d : ℝ) - (a : ℝ)) = ((d - a : ℕ) : ℝ) := by
        exact (Nat.cast_sub had).symm
      rw [hcast]
    have hA2_from_common_counts
        (d a : ℕ) (had : a ≤ d)
        (hcounts : ∀ u : Projectivization K (Fin (t + 1) → K),
          (Finset.univ.filter
            (fun w => PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).card =
            if u = v0 then d else a) :
        LoopGraphAdjacencyAction (PolarityGraph K t)
            (fun v => LoopGraphAdjacencyAction (PolarityGraph K t) f v) v0 =
          (((d - a : ℕ) : ℝ) * f v0) := by
      rw [hA2_common]
      trans Finset.univ.sum
          (fun u : Projectivization K (Fin (t + 1) → K) =>
            ((if u = v0 then d else a : ℕ) : ℝ) * f u)
      · apply Finset.sum_congr rfl
        intro u _
        rw [hcounts u]
      · exact hcommon_sum_zero d a had
    have hmu_sq_common :
        mu ^ 2 * f v0 =
          Finset.univ.sum
            (fun u =>
              (((Finset.univ.filter
                (fun w => PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).card : ℕ) : ℝ) *
                f u) := by
      rw [← hA2_eig, hA2_common]
    have hdiag_common_eq_degree :
        (Finset.univ.filter
          (fun w : Projectivization K (Fin (t + 1) → K) =>
            PolarityGraph K t v0 w ∧ PolarityGraph K t w v0)).card =
          LoopGraphDegree (PolarityGraph K t) v0 := by
      dsimp [LoopGraphDegree, PolarityGraph]
      simp [Projectivization.orthogonal_comm]
      rfl
    have hdiag_common_count :
        (Finset.univ.filter
          (fun w : Projectivization K (Fin (t + 1) → K) =>
            PolarityGraph K t v0 w ∧ PolarityGraph K t w v0)).card =
          ((q ^ t - 1) / (q - 1)) := by
      rw [hdiag_common_eq_degree, hdegree v0]
    have hrep_linearIndependent_of_ne
        (u : Projectivization K (Fin (t + 1) → K)) (hu : u ≠ v0) :
        LinearIndependent K ![Projectivization.rep v0, Projectivization.rep u] := by
      exact (Projectivization.linearIndependent_pair_iff_ne).mpr hu.symm
    have hcommon_rep_iff
        (u w : Projectivization K (Fin (t + 1) → K)) :
        PolarityGraph K t v0 w ∧ PolarityGraph K t w u ↔
          Projectivization.rep v0 ⬝ᵥ Projectivization.rep w = 0 ∧
            Projectivization.rep u ⬝ᵥ Projectivization.rep w = 0 := by
      constructor
      · intro h
        constructor
        · have hmk :
              Projectivization.orthogonal
                (Projectivization.mk K (Projectivization.rep v0)
                  (Projectivization.rep_nonzero v0))
                (Projectivization.mk K (Projectivization.rep w)
                  (Projectivization.rep_nonzero w)) := by
            simpa [Projectivization.mk_rep, PolarityGraph] using h.1
          exact (Projectivization.orthogonal_mk
            (Projectivization.rep_nonzero v0) (Projectivization.rep_nonzero w)).mp hmk
        · have hmk :
              Projectivization.orthogonal
                (Projectivization.mk K (Projectivization.rep u)
                  (Projectivization.rep_nonzero u))
                (Projectivization.mk K (Projectivization.rep w)
                  (Projectivization.rep_nonzero w)) := by
            have huw : PolarityGraph K t u w :=
              Projectivization.orthogonal_comm.mp h.2
            simpa [Projectivization.mk_rep, PolarityGraph] using huw
          exact (Projectivization.orthogonal_mk
            (Projectivization.rep_nonzero u) (Projectivization.rep_nonzero w)).mp hmk
      · intro h
        constructor
        · have hmk :
              Projectivization.orthogonal
                (Projectivization.mk K (Projectivization.rep v0)
                  (Projectivization.rep_nonzero v0))
                (Projectivization.mk K (Projectivization.rep w)
                  (Projectivization.rep_nonzero w)) :=
            (Projectivization.orthogonal_mk
              (Projectivization.rep_nonzero v0) (Projectivization.rep_nonzero w)).mpr h.1
          simpa [Projectivization.mk_rep, PolarityGraph] using hmk
        · have hmk :
              Projectivization.orthogonal
                (Projectivization.mk K (Projectivization.rep u)
                  (Projectivization.rep_nonzero u))
                (Projectivization.mk K (Projectivization.rep w)
                  (Projectivization.rep_nonzero w)) :=
            (Projectivization.orthogonal_mk
              (Projectivization.rep_nonzero u) (Projectivization.rep_nonzero w)).mpr h.2
          have huw : PolarityGraph K t u w := by
            simpa [Projectivization.mk_rep, PolarityGraph] using hmk
          exact Projectivization.orthogonal_comm.mp huw
    let commonNeighborFunctional (u : Projectivization K (Fin (t + 1) → K)) :
        (Fin (t + 1) → K) →ₗ[K] (Fin 2 → K) :=
      { toFun := fun z =>
          ![Projectivization.rep v0 ⬝ᵥ z, Projectivization.rep u ⬝ᵥ z]
        map_add' := by
          intro z z'
          ext i
          fin_cases i <;> simp [dotProduct_add]
        map_smul' := by
          intro a z
          ext i
          fin_cases i <;> simp [dotProduct_smul] }
    have hcommonNeighborFunctional_ker
        (u : Projectivization K (Fin (t + 1) → K)) :
        LinearMap.ker (commonNeighborFunctional u) =
          { z : Fin (t + 1) → K |
            Projectivization.rep v0 ⬝ᵥ z = 0 ∧ Projectivization.rep u ⬝ᵥ z = 0 } := by
      ext z
      simp [commonNeighborFunctional]
    have hcommonNeighborFunctional_range
        (u : Projectivization K (Fin (t + 1) → K)) :
        ∃ ψ : Projectivization K (LinearMap.ker (commonNeighborFunctional u)) →
            Projectivization K (Fin (t + 1) → K),
          Function.Injective ψ ∧
            Set.range ψ =
              { w : Projectivization K (Fin (t + 1) → K) |
                PolarityGraph K t v0 w ∧ PolarityGraph K t w u } := by
      let Φ := commonNeighborFunctional u
      let ι : Φ.ker →ₗ[K] (Fin (t + 1) → K) := Φ.ker.subtype
      have hι_inj : Function.Injective ι := Φ.ker.injective_subtype
      let ψ : Projectivization K Φ.ker → Projectivization K (Fin (t + 1) → K) :=
        Projectivization.map ι hι_inj
      refine ⟨ψ, Projectivization.map_injective ι hι_inj, ?_⟩
      ext w
      constructor
      · rintro ⟨z, rfl⟩
        induction z using Projectivization.ind with
        | h y hy =>
          change PolarityGraph K t v0
              (Projectivization.map ι hι_inj (Projectivization.mk K y hy)) ∧
            PolarityGraph K t
              (Projectivization.map ι hι_inj (Projectivization.mk K y hy)) u
          rw [Projectivization.map_mk]
          have hyι : ι y ≠ 0 := by
            intro hzero
            exact hy (hι_inj (by simpa using hzero))
          constructor
          · have hy0 : Projectivization.rep v0 ⬝ᵥ (y : Fin (t + 1) → K) = 0 := by
              have h0 := congr_fun (show Φ y = 0 from y.property) (0 : Fin 2)
              change Projectivization.rep v0 ⬝ᵥ (y : Fin (t + 1) → K) = 0 at h0
              exact h0
            have hmk :
                Projectivization.orthogonal
                  (Projectivization.mk K (Projectivization.rep v0)
                    (Projectivization.rep_nonzero v0))
                  (Projectivization.mk K (ι y) hyι) :=
              (Projectivization.orthogonal_mk
                (Projectivization.rep_nonzero v0) hyι).mpr hy0
            simpa [Projectivization.mk_rep, PolarityGraph] using hmk
          · have hyu : Projectivization.rep u ⬝ᵥ (y : Fin (t + 1) → K) = 0 := by
              have h1 := congr_fun (show Φ y = 0 from y.property) (1 : Fin 2)
              change Projectivization.rep u ⬝ᵥ (y : Fin (t + 1) → K) = 0 at h1
              exact h1
            have hmk :
                Projectivization.orthogonal
                  (Projectivization.mk K (Projectivization.rep u)
                    (Projectivization.rep_nonzero u))
                  (Projectivization.mk K (ι y) hyι) :=
              (Projectivization.orthogonal_mk
                (Projectivization.rep_nonzero u) hyι).mpr hyu
            have huw : PolarityGraph K t u (Projectivization.mk K (ι y) hyι) := by
              simpa [Projectivization.mk_rep, PolarityGraph] using hmk
            exact Projectivization.orthogonal_comm.mp huw
      · intro hw
        induction w using Projectivization.ind with
        | h z hz =>
          have hz0 : Projectivization.rep v0 ⬝ᵥ z = 0 := by
            have hmk :
                Projectivization.orthogonal
                  (Projectivization.mk K (Projectivization.rep v0)
                    (Projectivization.rep_nonzero v0))
                  (Projectivization.mk K z hz) := by
              simpa [Projectivization.mk_rep, PolarityGraph] using hw.1
            exact (Projectivization.orthogonal_mk
              (Projectivization.rep_nonzero v0) hz).mp hmk
          have hzu : Projectivization.rep u ⬝ᵥ z = 0 := by
            have huw : PolarityGraph K t u (Projectivization.mk K z hz) :=
              Projectivization.orthogonal_comm.mp hw.2
            have hmk :
                Projectivization.orthogonal
                  (Projectivization.mk K (Projectivization.rep u)
                    (Projectivization.rep_nonzero u))
                  (Projectivization.mk K z hz) := by
              simpa [Projectivization.mk_rep, PolarityGraph] using huw
            exact (Projectivization.orthogonal_mk
              (Projectivization.rep_nonzero u) hz).mp hmk
          have hzker : z ∈ Φ.ker := by
            change commonNeighborFunctional u z = 0
            ext i
            fin_cases i
            · exact hz0
            · exact hzu
          refine ⟨Projectivization.mk K (⟨z, hzker⟩ : Φ.ker) ?_, ?_⟩
          · intro hzero
            exact hz (congrArg Subtype.val hzero)
          · change Projectivization.map ι hι_inj
                (Projectivization.mk K (⟨z, hzker⟩ : Φ.ker) ?_) =
              Projectivization.mk K z hz
            rw [Projectivization.map_mk]
            rfl
    have htoDual_dot
        (x z : Fin (t + 1) → K) :
        ((Pi.basisFun K (Fin (t + 1))).toDualEquiv x) z = x ⬝ᵥ z := by
      let b := Pi.basisFun K (Fin (t + 1))
      rw [Module.Basis.toDualEquiv_apply]
      change b.toDual x z = x ⬝ᵥ z
      calc
        b.toDual x z = b.toDual x (∑ i, z i • b i) := by
          have hzsum : (∑ i, z i • b i) = z := by
            simpa [b] using b.sum_repr z
          rw [hzsum]
        _ = ∑ i, z i * (b.toDual x (b i)) := by
          simp [map_sum, smul_eq_mul]
        _ = ∑ i, z i * x i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [Module.Basis.toDual_apply_left]
          simp [b]
        _ = x ⬝ᵥ z := by
          rw [dotProduct]
          apply Finset.sum_congr rfl
          intro i _
          ring
    have hcommonNeighborFunctional_surjective
        (u : Projectivization K (Fin (t + 1) → K)) (hu : u ≠ v0) :
        Function.Surjective (commonNeighborFunctional u) := by
      let V := Fin (t + 1) → K
      let b := Pi.basisFun K (Fin (t + 1))
      let rowDual : Fin 2 → Module.Dual K V :=
        fun i => b.toDualEquiv (![Projectivization.rep v0, Projectivization.rep u] i)
      have hrowDual_li : LinearIndependent K rowDual := by
        have hmap := (hrep_linearIndependent_of_ne u hu).map'
          (f := b.toDualEquiv.toLinearMap) (by simp)
        simpa [rowDual] using hmap
      let rowFun : Fin 2 → V → K := fun i z => rowDual i z
      have hrowFun_li : LinearIndependent K rowFun := by
        rw [Fintype.linearIndependent_iff] at hrowDual_li ⊢
        intro g hg i
        apply hrowDual_li g
        apply LinearMap.ext
        intro z
        have hz := congr_fun hg z
        simpa [rowFun] using hz
      have hspan : Submodule.span K (Set.range (flip rowFun)) = ⊤ := by
        exact (span_flip_eq_top_iff_linearIndependent (f := rowFun)).mpr hrowFun_li
      have hrange :
          LinearMap.range (commonNeighborFunctional u) =
            Submodule.span K (Set.range (flip rowFun)) := by
        apply le_antisymm
        · intro w hw
          rcases hw with ⟨z, rfl⟩
          apply Submodule.subset_span
          refine ⟨z, ?_⟩
          ext i
          fin_cases i
          · simpa [commonNeighborFunctional, rowFun, rowDual] using
              (htoDual_dot (Projectivization.rep v0) z)
          · simpa [commonNeighborFunctional, rowFun, rowDual] using
              (htoDual_dot (Projectivization.rep u) z)
        · apply Submodule.span_le.mpr
          rintro w ⟨z, rfl⟩
          refine ⟨z, ?_⟩
          ext i
          fin_cases i
          · simpa [commonNeighborFunctional, rowFun, rowDual] using
              (htoDual_dot (Projectivization.rep v0) z).symm
          · simpa [commonNeighborFunctional, rowFun, rowDual] using
              (htoDual_dot (Projectivization.rep u) z).symm
      exact LinearMap.range_eq_top.mp (by rw [hrange, hspan])
    have hcommonNeighborFunctional_finrank
        (u : Projectivization K (Fin (t + 1) → K)) (hu : u ≠ v0) :
        Module.finrank K (LinearMap.ker (commonNeighborFunctional u)) = t - 1 := by
      let Φ := commonNeighborFunctional u
      have hsurj : Function.Surjective Φ :=
        hcommonNeighborFunctional_surjective u hu
      have hΦ_range : LinearMap.range Φ = ⊤ :=
        LinearMap.range_eq_top.mpr hsurj
      have hrange_finrank : Module.finrank K (LinearMap.range Φ) = 2 := by
        rw [hΦ_range]
        simp [Module.finrank_fintype_fun_eq_card]
      have hdomain_finrank :
          Module.finrank K (Fin (t + 1) → K) = t + 1 := by
        simp [Module.finrank_fintype_fun_eq_card]
      have hranknull := LinearMap.finrank_range_add_finrank_ker Φ
      rw [hrange_finrank, hdomain_finrank] at hranknull
      have hright : t + 1 = 2 + (t - 1) := by
        omega
      have hkplus :
          2 + Module.finrank K (LinearMap.ker Φ) =
            2 + (t - 1) := by
        rw [hranknull, hright]
      exact Nat.add_left_cancel hkplus
    have hoffdiag_common_count
        (u : Projectivization K (Fin (t + 1) → K)) (hu : u ≠ v0) :
        (Finset.univ.filter
          (fun w : Projectivization K (Fin (t + 1) → K) =>
            PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).card =
          ((q ^ (t - 1) - 1) / (q - 1)) := by
      have hfilter_subtype :
          (Finset.univ.filter
            (fun w : Projectivization K (Fin (t + 1) → K) =>
              PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).card =
            Fintype.card
              { w : Projectivization K (Fin (t + 1) → K) //
                PolarityGraph K t v0 w ∧ PolarityGraph K t w u } := by
        simpa using (Fintype.card_subtype
          (fun w : Projectivization K (Fin (t + 1) → K) =>
            PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).symm
      rcases hcommonNeighborFunctional_range u with ⟨ψ, hψ_inj, hψ_range⟩
      haveI : Fintype (LinearMap.ker (commonNeighborFunctional u)) :=
        Fintype.ofFinite (LinearMap.ker (commonNeighborFunctional u))
      haveI : Fintype (Projectivization K (LinearMap.ker (commonNeighborFunctional u))) :=
        Fintype.ofFinite (Projectivization K (LinearMap.ker (commonNeighborFunctional u)))
      have hsubtype_card :
          Fintype.card
              { w : Projectivization K (Fin (t + 1) → K) //
                PolarityGraph K t v0 w ∧ PolarityGraph K t w u } =
            Fintype.card
              (Projectivization K (LinearMap.ker (commonNeighborFunctional u))) := by
        let eRange :
            Projectivization K (LinearMap.ker (commonNeighborFunctional u)) ≃
              Set.range ψ :=
          Equiv.ofInjective ψ hψ_inj
        let eSet : Set.range ψ ≃
            { w : Projectivization K (Fin (t + 1) → K) //
              PolarityGraph K t v0 w ∧ PolarityGraph K t w u } :=
          Equiv.setCongr hψ_range
        exact (Fintype.card_congr (eRange.trans eSet)).symm
      have hker_card :
          Nat.card (LinearMap.ker (commonNeighborFunctional u)) = q ^ (t - 1) := by
        rw [Module.natCard_eq_pow_finrank
          (K := K) (V := LinearMap.ker (commonNeighborFunctional u))]
        rw [hcommonNeighborFunctional_finrank u hu]
        rw [Nat.card_eq_fintype_card (α := K), ← hq]
      rw [hfilter_subtype, hsubtype_card]
      rw [← Nat.card_eq_fintype_card]
      rw [Projectivization.card'']
      rw [hker_card]
      rw [Nat.card_eq_fintype_card (α := K), ← hq]
    have hcounts :
        ∀ u : Projectivization K (Fin (t + 1) → K),
          (Finset.univ.filter
            (fun w : Projectivization K (Fin (t + 1) → K) =>
              PolarityGraph K t v0 w ∧ PolarityGraph K t w u)).card =
            if u = v0 then ((q ^ t - 1) / (q - 1))
            else ((q ^ (t - 1) - 1) / (q - 1)) := by
      intro u
      by_cases hu : u = v0
      · subst u
        simp [hdiag_common_count]
      · simp [hu, hoffdiag_common_count u hu]
    have had :
        ((q ^ (t - 1) - 1) / (q - 1)) ≤ ((q ^ t - 1) / (q - 1)) := by
      have hqpos : 0 < q := by
        rw [hq]
        exact Fintype.card_pos
      have hqone : 1 ≤ q := Nat.succ_le_of_lt hqpos
      have hpow_le : q ^ (t - 1) ≤ q ^ t :=
        Nat.pow_le_pow_right hqone (Nat.sub_le t 1)
      exact Nat.div_le_div_right (Nat.sub_le_sub_right hpow_le 1)
    have hA2_value :
        LoopGraphAdjacencyAction (PolarityGraph K t)
            (fun v => LoopGraphAdjacencyAction (PolarityGraph K t) f v) v0 =
          ((((q ^ t - 1) / (q - 1)) -
            ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ) * f v0 :=
      hA2_from_common_counts
        ((q ^ t - 1) / (q - 1))
        ((q ^ (t - 1) - 1) / (q - 1)) had hcounts
    have hmu_sq_mul :
        mu ^ 2 * f v0 =
          ((((q ^ t - 1) / (q - 1)) -
            ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ) * f v0 :=
      hA2_eig.symm.trans hA2_value
    have hmu_sq :
        mu ^ 2 =
          ((((q ^ t - 1) / (q - 1)) -
            ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ) := by
      exact (mul_left_inj' hv0).mp hmu_sq_mul
    have hsq_le :
        mu ^ 2 ≤
          ((((q ^ t - 1) / (q - 1)) -
            ((q ^ (t - 1) - 1) / (q - 1)) : ℕ) : ℝ) := by
      rw [hmu_sq]
    exact Real.abs_le_sqrt hsq_le
  · exact Real.sqrt_nonneg _
