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
  · classical
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
    sorry
  · exact Real.sqrt_nonneg _
