/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.IntegralOperators
public import PrimeGapsTheory.Variational.Integration.Simplex
public import PrimeGapsTheory.Variational.SmoothApprox

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Integral formulas for the variational operators

Expresses the norm and marginal quadratic forms of polynomial functions as simplex integrals.

## Main results

* `powerSumListMoment_integral`: Evaluates products of arbitrary power sums.
* `lem_Ik_quadratic_I`: Evaluates the norm quadratic form of a polynomial.
* `J_toLp_eq_iterated`: Expresses a marginal quadratic form as an iterated integral.
-/

@[expose] public section

open scoped ENNReal
open scoped Nat

open scoped PrimeGaps RealInnerProductSpace
open MeasureTheory EuclideanSpace

namespace PrimeGaps

/-- The exponent of coordinate `i` obtained by assigning the entries of `L` to coordinates
according to `c`. -/
def powerSumColouringExponent {k : ℕ} (L : List ℕ) (c : Fin L.length → Fin k) (i : Fin k) : ℕ :=
  ∑ j : Fin L.length, if c j = i then L.get j else 0

/-- The numerator in the Dirichlet integral of a product of power sums. -/
def powerSumListMoment (k : ℕ) (L : List ℕ) : ℕ :=
  ∑ c : Fin L.length → Fin k, ∏ i : Fin k, (powerSumColouringExponent L c i)!

/-- A colouring redistributes the entries of `L` without loss: `∑ i, powerSumColouringExponent L c i
= L.sum`. -/
theorem powerSumColouringExponent_sum {k : ℕ} (L : List ℕ) (c : Fin L.length → Fin k) :
    ∑ i : Fin k, powerSumColouringExponent L c i = L.sum := by
  classical
  unfold powerSumColouringExponent
  rw [Finset.sum_comm]
  have hin : ∀ j : Fin L.length, ∑ i : Fin k, (if c j = i then L.get j else 0) = L.get j := by
    intro j
    rw [Finset.sum_eq_single (c j)]
    · simp
    · intro i _ hi
      simp [Ne.symm hi]
    · simp
  simp_rw [hin]
  rw [← List.sum_ofFn, List.ofFn_get]

/-- Expanding a product of power sums over colourings:
`∏_{r ∈ L} (∑ i, xᵢ ^ r) = ∑ c, ∏ i, xᵢ ^ powerSumColouringExponent L c i`. -/
theorem powerSumProd_expand {k : ℕ} (L : List ℕ) (x : EuclideanSpace ℝ (Fin k)) :
    (L.map (fun r ↦ ∑ i, (x i) ^ r)).prod = ∑ c : Fin L.length → Fin k,
      ∏ i : Fin k, (x i) ^ powerSumColouringExponent L c i := by
  classical
  calc
    (L.map (fun r ↦ ∑ i, (x i) ^ r)).prod =
        ∏ j : Fin L.length, ∑ i : Fin k, (x i) ^ L.get j := by
      rw [← List.prod_ofFn]
      congr 1
      calc
        L.map (fun r ↦ ∑ i, (x i) ^ r) =
            (List.ofFn L.get).map (fun r ↦ ∑ i, (x i) ^ r) := by
          rw [List.ofFn_get]
        _ = List.ofFn ((fun r ↦ ∑ i, (x i) ^ r) ∘ L.get) := List.map_ofFn
        _ = List.ofFn (fun j ↦ ∑ i, (x i) ^ L.get j) := rfl
    _ = ∑ c : Fin L.length → Fin k, ∏ j, (x (c j)) ^ L.get j := by
      rw [Fintype.prod_sum]
    _ = ∑ c : Fin L.length → Fin k,
        ∏ i : Fin k, (x i) ^ powerSumColouringExponent L c i := by
      apply Finset.sum_congr rfl
      intro c _
      rw [← Finset.prod_fiberwise Finset.univ c (fun j ↦ (x (c j)) ^ L.get j)]
      apply Finset.prod_congr rfl
      intro i _
      calc
        ∏ j with c j = i, (x (c j)) ^ L.get j =
            ∏ j with c j = i, (x i) ^ L.get j := by
          apply Finset.prod_congr rfl
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          rw [hj]
        _ = (x i) ^ ∑ j with c j = i, L.get j := Finset.prod_pow_eq_pow_sum _ _ _
        _ = (x i) ^ powerSumColouringExponent L c i := by
          congr 1
          simp [powerSumColouringExponent, Finset.sum_filter]

/-- Dirichlet integration of an arbitrary finite product of power sums. -/
theorem powerSumListMoment_integral (k a : ℕ) (L : List ℕ) :
    (∫ x in 𝓡 k, (1 - ∑ i, x i) ^ a * (L.map (fun r ↦ ∑ i, (x i) ^ r)).prod) =
      (a ! : ℝ) * powerSumListMoment k L /
        ((k + a + L.sum)! : ℝ) := by
  classical
  have hcpt : IsCompact (𝓡 k) := EuclideanSpace.isCompact_scaledStdSimplex
  simp_rw [powerSumProd_expand L]
  have hmul : (fun x : EuclideanSpace ℝ (Fin k) ↦ (1 - ∑ i, x i) ^ a * ∑ c : Fin L.length → Fin k,
          ∏ i : Fin k, (x i) ^ powerSumColouringExponent L c i) =
        fun x ↦ ∑ c : Fin L.length → Fin k, (1 - ∑ i, x i) ^ a *
          ∏ i : Fin k, (x i) ^ powerSumColouringExponent L c i := by
    funext x
    rw [Finset.mul_sum]
  rw [hmul, MeasureTheory.integral_finsetSum _ (fun c _ ↦
    ContinuousOn.integrableOn_compact hcpt (by fun_prop))]
  have hterm : ∀ c : Fin L.length → Fin k, (∫ x in 𝓡 k, (1 - ∑ i, x i) ^ a *
        ∏ i, (x i) ^ powerSumColouringExponent L c i) = (a ! : ℝ) *
            (∏ i, ((powerSumColouringExponent L c i)! : ℝ)) /
              ((k + a + L.sum)! : ℝ) := by
    intro c
    rw [dirichlet_integral k a (powerSumColouringExponent L c), powerSumColouringExponent_sum L c]
    simp only [Nat.cast_prod]
  simp_rw [hterm, div_eq_mul_inv]
  rw [← Finset.sum_mul, ← Finset.mul_sum]
  simp only [powerSumListMoment, Nat.cast_sum, Nat.cast_prod]

/-- For a product of copies of `P₂`, the list moment is `maynardG`. -/
theorem powerSumListMoment_replicate_two (k b : ℕ) :
    powerSumListMoment k (List.replicate b 2) = maynardG b 2 k := by
  have hlist := powerSumListMoment_integral k 0 (List.replicate b 2)
  have hmaynard := lem_integration_formula k 0 b
  simp only [List.map_replicate, List.prod_replicate, List.sum_replicate, nsmul_eq_mul,
    Nat.factorial_zero, Nat.cast_one, one_mul] at hlist hmaynard
  have hden : (0 : ℝ) < ((k + 2 * b)! : ℕ) := by positivity
  have hcast : (powerSumListMoment k (List.replicate b 2) : ℝ) = maynardG b 2 k := by
    apply (div_left_inj' hden.ne').mp
    simpa [Nat.mul_comm] using hlist.symm.trans hmaynard
  exact_mod_cast hcast

/-- Cross-term integrability over the compact simplex `𝓡 k`. -/
theorem term_int_R (k d : ℕ) (a : Fin d → ℝ) (b c : Fin d → ℕ) (i j : Fin d) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin k) ↦
      (a i * (1 - ∑ ℓ, x ℓ) ^ (b i) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i)) *
      (a j * (1 - ∑ ℓ, x ℓ) ^ (b j) * (∑ ℓ, (x ℓ) ^ 2) ^ (c j))) (𝓡 k) volume :=
  (Continuous.continuousOn (by fun_prop)).integrableOn_compact
    (EuclideanSpace.isCompact_scaledStdSimplex (k := k) (s := 1))

/-- The integral of the square of `polyP` over `𝓡 k` equals its quadratic form. -/
theorem intP_closed_R (k d : ℕ) (a : Fin d → ℝ) (b c : Fin d → ℕ) :
    (∫ x in 𝓡 k, (∑ i, a i * (1 - ∑ ℓ, x ℓ) ^ (b i) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i)) ^ 2) =
    ∑ i, ∑ j, a i * a j * ((b i + b j)! : ℝ) * (maynardG (c i + c j) 2 k : ℝ) /
        ((k + b i + b j + 2 * c i + 2 * c j)! : ℝ) := by
  have h2 : ∀ x : EuclideanSpace ℝ (Fin k),
      (∑ i, a i * (1 - ∑ ℓ, x ℓ) ^ (b i) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i)) ^ 2 =
      ∑ i, ∑ j, (a i * (1 - ∑ ℓ, x ℓ) ^ (b i) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i)) *
                  (a j * (1 - ∑ ℓ, x ℓ) ^ (b j) * (∑ ℓ, (x ℓ) ^ 2) ^ (c j)) := by
    intro x; rw [sq, Finset.sum_mul_sum]
  rw [MeasureTheory.setIntegral_congr_fun
        (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).measurableSet (fun x _ ↦ h2 x),
    MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl; intro i _
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl; intro j _
      have hcomb : ∀ x : EuclideanSpace ℝ (Fin k),
          (a i * (1 - ∑ ℓ, x ℓ) ^ (b i) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i)) *
          (a j * (1 - ∑ ℓ, x ℓ) ^ (b j) * (∑ ℓ, (x ℓ) ^ 2) ^ (c j)) =
          (a i * a j) * ((1 - ∑ ℓ, x ℓ) ^ (b i + b j) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i + c j)) := by
        intro x; rw [pow_add, pow_add]; ring
      have hformula : (∫ x in 𝓡 k, (1 - ∑ ℓ, x ℓ) ^ (b i + b j) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i + c j)) =
            ((b i + b j)! : ℝ) * (maynardG (c i + c j) 2 k : ℝ) /
              ((k + (b i + b j) + 2 * (c i + c j))! : ℝ) := by
        simpa only [IsFactorialMoment] using (lem_integration_formula k (b i + b j) (c i + c j))
      rw [MeasureTheory.setIntegral_congr_fun
            (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).measurableSet
              (fun x _ ↦ hcomb x),
        MeasureTheory.integral_const_mul, hformula,
        show k + (b i + b j) + 2 * (c i + c j) = k + b i + b j + 2 * c i + 2 * c j from by ring]
      ring
    · intro j _; exact term_int_R k d a b c i j
  · intro i _
    apply MeasureTheory.integrable_finsetSum
    intro j _; exact term_int_R k d a b c i j

/-- The squared `L²` norm equals the integral of the square. -/
theorem I_toLp_eq (k : ℕ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : MemLp F 2 (volume.restrict (𝓡 k))) :
    ‖hF.toLp F‖ ^ 2 = ∫ x in 𝓡 k, (F x) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with a ha
  rw [ha, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- The polynomial belongs to `L²(𝓡 k)`. -/
theorem polyP_memLp (k d : ℕ) (a : Fin d → ℝ) (b c : Fin d → ℕ) :
    MemLp (fun x : EuclideanSpace ℝ (Fin k) ↦
      ∑ i, a i * (1 - ∑ ℓ, x ℓ) ^ (b i) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i)) 2
      (volume.restrict (𝓡 k)) := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦
      ∑ i, a i * (1 - ∑ ℓ, x ℓ) ^ (b i) * (∑ ℓ, (x ℓ) ^ 2) ^ (c i)) := by fun_prop
  haveI : IsFiniteMeasure (volume.restrict (𝓡 k)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (EuclideanSpace.isCompact_scaledStdSimplex (k := k) (s := 1)).measure_lt_top⟩
  obtain ⟨C, hC⟩ :=
    (EuclideanSpace.isCompact_scaledStdSimplex (k := k) (s := 1)).exists_bound_of_continuousOn
      hc.continuousOn
  refine MemLp.of_bound hc.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).measurableSet]
  exact Filter.Eventually.of_forall hC

/-- The squared norm of the polynomial witness equals its closed-form quadratic form. -/
@[pg_tag "bg246" "lem_Ik_quadratic"]
theorem lem_Ik_quadratic_I (k d : ℕ) (a : Fin d → ℝ) (b c : Fin d → ℕ) :
    ‖(polyP_memLp k d a b c).toLp _‖ ^ 2 =
    ∑ i, ∑ j, a i * a j * ((b i + b j)! : ℝ) * (maynardG (c i + c j) 2 k : ℝ) /
        ((k + b i + b j + 2 * c i + 2 * c j)! : ℝ) := by
  rw [I_toLp_eq, intP_closed_R k d a b c]

/-- Coordinate reassembly: `finIsolateEquivProd⁻¹ (y, t)` re-inserts the isolated coordinate `t 0`
at position `m`, giving `Fin.insertNth m (t 0) y`.
-/
theorem symm_finIsolate_apply (n : ℕ) (m : Fin (n + 1))
    (y : EuclideanSpace ℝ (Fin n)) (t : EuclideanSpace ℝ (Fin 1)) :
    ((finIsolateEquivProd ℝ m).symm (y, t)) = WithLp.toLp 2 (m.insertNth (t 0) (fun j ↦ y j)) := by
  have hinl : ∀ s : Fin n, (Fin.finIsolateEquivSum m).symm (Sum.inl s) = m.succAbove s := by
    intro s
    apply Fin.ext
    simp only [Fin.finIsolateEquivSum, Equiv.coe_fn_symm_mk, Sum.elim_inl, Fin.succAbove,
      Fin.lt_def, Fin.val_castSucc, Fin.val_succ, apply_ite Fin.val]
  have hinr : (Fin.finIsolateEquivSum m).symm (Sum.inr 0) = m := by
    simp only [Fin.finIsolateEquivSum, Equiv.coe_fn_symm_mk, Sum.elim_inr, Matrix.cons_val_zero]
  rw [ContinuousLinearEquiv.symm_apply_eq]
  simp only [finIsolateEquivProd, EuclideanSpace.sumEquivProd,
    ContinuousLinearEquiv.trans_apply, LinearIsometryEquiv.coe_toContinuousLinearEquiv]
  ext s
  all_goals simp only [WithLp.prodContinuousLinearEquiv_apply,
    PiLp.sumPiLpEquivProdLpPiLp_apply_ofLp, LinearIsometryEquiv.piLpCongrLeft_apply,
    Equiv.piCongrLeft'_apply, WithLp.ofLp_toLp]
  · rw [hinl s, Fin.insertNth_apply_succAbove]
  · obtain rfl : s = 0 := Subsingleton.elim s 0
    rw [hinr, Fin.insertNth_apply_same]

/-- Concrete coefficient function of `Lp.integralLeftCLM`. -/
theorem coeFn_integralLeftCLM {p : ℝ≥0∞} {E α β : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace α] [MeasurableSpace β]
    {mu : Measure α} {nu : Measure β} [SFinite nu] [Fact (1 ≤ p)]
    {S : Set (α × β)} (hMS : MeasurableSet S) (hS : EssFiniteSnd S mu nu)
    (f : Lp E p ((mu.prod nu).restrict S)) :
    Lp.integralLeftCLM hMS hS f =ᵐ[mu] fun x ↦ ∫ y, S.indicator f (x, y) ∂nu :=
  MemLp.coeFn_toLp (memLp_integral_left hMS hS Fact.out (Lp.memLp f))

/-- Concrete coefficient function of `Lp.integralVarCLM`. -/
theorem coeFn_integralVarCLM {k : ℕ} (m : Fin k) {S : Set (EuclideanSpace ℝ (Fin k))}
    (hMS : MeasurableSet S)
    (hS : EssFiniteSnd (finIsolateEquivProd ℝ m '' S) volume volume)
    (f : Lp ℝ 2 (volume.restrict S)) :
    Lp.integralVarCLM m hMS hS f =ᵐ[volume] fun y : EuclideanSpace ℝ (Fin (k - 1)) ↦
      ∫ t : EuclideanSpace ℝ (Fin 1), (finIsolateEquivProd ℝ m '' S).indicator
          (fun z ↦ f ((finIsolateEquivProd ℝ m).symm z)) (y, t) ∂volume := by
  have hf : MeasurePreserving (finIsolateEquivProd ℝ m).symm
      (volume.restrict (finIsolateEquivProd ℝ m '' S)) (volume.restrict S) := by
    have h := (measurePreserving_symm_finIsolateEquivProd m).restrict_preimage hMS
    rwa [← (finIsolateEquivProd ℝ m).image_eq_preimage_symm] at h
  set g := (Lp.compMeasurePreservingₗᵢ ℝ _ hf).toContinuousLinearMap f with hg
  have himg : MeasurableSet (finIsolateEquivProd ℝ m '' S) :=
    (finIsolateEquivProd ℝ m).toHomeomorph.measurableEmbedding.measurableSet_image.mpr hMS
  have hstep1 : Lp.integralVarCLM m hMS hS f = Lp.integralLeftCLM himg hS g := rfl
  rw [Filter.EventuallyEq, hstep1]
  have h1 := coeFn_integralLeftCLM himg hS g
  have h2 : (g : EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin 1) → ℝ)
      =ᵐ[volume.restrict (finIsolateEquivProd ℝ m '' S)]
        fun z ↦ f ((finIsolateEquivProd ℝ m).symm z) :=
    Lp.coeFn_compMeasurePreserving f hf
  have h3 : (finIsolateEquivProd ℝ m '' S).indicator (g : _ → ℝ)
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin 1)))]
        (finIsolateEquivProd ℝ m '' S).indicator
          (fun z ↦ f ((finIsolateEquivProd ℝ m).symm z)) := by
    filter_upwards [(ae_restrict_iff' himg).mp h2] with z hz
    by_cases hzS : z ∈ finIsolateEquivProd ℝ m '' S
    · simp [Set.indicator_of_mem hzS, hz hzS]
    · simp [Set.indicator_of_notMem hzS]
  filter_upwards [h1, Measure.ae_ae_of_ae_prod h3] with y hy hfiber
  rw [hy]
  exact integral_congr_ae hfiber

/-- The marginal functional `J m f` as an explicit iterated integral. -/
theorem J_marginal {k : ℕ} (m : Fin k) (f : Lp ℝ 2 (volume.restrict (𝓡 k))) :
    PrimeGaps.J m f = ∫ y : EuclideanSpace ℝ (Fin (k - 1)), (∫ t : EuclideanSpace ℝ (Fin 1),
        (finIsolateEquivProd ℝ m '' (𝓡 k)).indicator
          (fun z ↦ f ((finIsolateEquivProd ℝ m).symm z)) (y, t) ∂volume) ^ 2 ∂volume := by
  rw [PrimeGaps.J_apply, PrimeGaps.JBilinCLM, EuclideanSpace.tonelliBilinCLM]
  simp only [ContinuousLinearMap.bilinearComp_apply, coe_innerSL_apply]
  rw [MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_integralVarCLM m
    (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).measurableSet
    (.of_isCompact (EuclideanSpace.isCompact_scaledStdSimplex (k := k) (s := 1))) f] with y hy
  rw [hy, RCLike.inner_apply, conj_trivial, ← sq]

/-- The marginal of a `toLp` witness equals its explicit iterated integral. -/
theorem J_marginal_toLp {k : ℕ} (m : Fin k) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : MemLp F 2 (volume.restrict (𝓡 k))) :
    PrimeGaps.J m (hF.toLp F) = ∫ y : EuclideanSpace ℝ (Fin (k - 1)),
      (∫ t : EuclideanSpace ℝ (Fin 1), (finIsolateEquivProd ℝ m '' (𝓡 k)).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z)) (y, t) ∂volume) ^ 2 ∂volume := by
  rw [J_marginal]
  have hf : MeasurePreserving (finIsolateEquivProd ℝ m).symm
      (volume.restrict (finIsolateEquivProd ℝ m '' (𝓡 k))) (volume.restrict (𝓡 k)) := by
    have h := (measurePreserving_symm_finIsolateEquivProd m).restrict_preimage
      (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).measurableSet
    rwa [← (finIsolateEquivProd ℝ m).image_eq_preimage_symm] at h
  have himg : MeasurableSet (finIsolateEquivProd ℝ m '' (𝓡 k)) :=
    (finIsolateEquivProd ℝ m).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).measurableSet
  have h3 : (finIsolateEquivProd ℝ m '' (𝓡 k)).indicator
        (fun z ↦ (hF.toLp F : EuclideanSpace ℝ (Fin k) → ℝ) ((finIsolateEquivProd ℝ m).symm z))
      =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin 1)))]
        (finIsolateEquivProd ℝ m '' (𝓡 k)).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z)) := by
    have hae : (fun z ↦ (hF.toLp F : _ → ℝ) ((finIsolateEquivProd ℝ m).symm z))
        =ᵐ[volume.restrict (finIsolateEquivProd ℝ m '' (𝓡 k))]
          fun z ↦ F ((finIsolateEquivProd ℝ m).symm z) :=
      hf.quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp
    filter_upwards [(ae_restrict_iff' himg).mp hae] with z hz
    by_cases hzS : z ∈ finIsolateEquivProd ℝ m '' (𝓡 k)
    · simp [Set.indicator_of_mem hzS, hz hzS]
    · simp [Set.indicator_of_notMem hzS]
  refine integral_congr_ae ?_
  filter_upwards [Measure.ae_ae_of_ae_prod h3] with y hfiber
  rw [integral_congr_ae hfiber]

/-- Integration over `EuclideanSpace ℝ (Fin 1)` agrees with integration over `ℝ`. -/
theorem integral_ES1 (G : ℝ → ℝ) : ∫ t : EuclideanSpace ℝ (Fin 1), G (t 0) = ∫ s : ℝ, G s := by
  rw [← (PiLp.volume_preserving_toLp (Fin 1)).integral_comp
        (MeasurableEquiv.toLp 2 (Fin 1 → ℝ)).measurableEmbedding (fun t ↦ G (t 0)),
    ← (volume_preserving_funUnique (Fin 1) ℝ).integral_comp
        (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding G]
  rfl

/-- `∑ i, (m.insertNth s g) i = s + ∑ j, g j`. -/
theorem insertNth_sum (n : ℕ) (m : Fin (n + 1)) (s : ℝ) (g : Fin n → ℝ) :
    ∑ i, (m.insertNth s g) i = s + ∑ j, g j := by
  rw [Fin.sum_univ_succAbove _ m]
  simp [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]

/-- Membership in the image of `𝓡 k` under `finIsolateEquivProd ℝ m` is membership of the preimage
under the inverse equivalence. -/
theorem mem_image_R_iff {k : ℕ} (m : Fin k)
    (z : EuclideanSpace ℝ (Fin (k - 1)) × EuclideanSpace ℝ (Fin 1)) :
    z ∈ finIsolateEquivProd ℝ m '' (𝓡 k) ↔ (finIsolateEquivProd ℝ m).symm z ∈ 𝓡 k := by
  rw [(finIsolateEquivProd ℝ m).image_eq_preimage_symm, Set.mem_preimage]

/-- The inner marginal at an admissible point equals its interval integral. -/
theorem inner_pointwise (n : ℕ) (m : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ)
    (y : EuclideanSpace ℝ (Fin (n + 1 - 1))) (hP : ∀ j, 0 ≤ y j) :
    (∫ t : EuclideanSpace ℝ (Fin 1), (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z).ofLp) (y, t)) =
      ∫ s in Set.Icc 0 (1 - ∑ j, y j), F (m.insertNth s (fun j ↦ y j)) := by
  have hint : ∀ t : EuclideanSpace ℝ (Fin 1), (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z).ofLp) (y, t) =
        (Set.Icc (0 : ℝ) (1 - ∑ j, y j)).indicator
            (fun s ↦ F (m.insertNth s (fun j ↦ y j))) (t 0) := by
    intro t
    have hval : F (((finIsolateEquivProd ℝ m).symm (y, t)).ofLp) =
        F (m.insertNth (t 0) (fun j ↦ y j)) := by
      rw [symm_finIsolate_apply]
    have hRiff : (finIsolateEquivProd ℝ m).symm (y, t) ∈ 𝓡 (n + 1) ↔
        (0 ≤ t 0 ∧ t 0 + ∑ j, y j ≤ 1) := by
      rw [symm_finIsolate_apply, EuclideanSpace.mem_scaledStdSimplex_iff]
      simp only []
      constructor
      · rintro ⟨h0, h1⟩
        exact ⟨by have := h0 m; rwa [Fin.insertNth_apply_same] at this,
               by rwa [insertNth_sum] at h1⟩
      · rintro ⟨ht, hsum⟩
        refine ⟨fun i ↦ ?_, ?_⟩
        · refine Fin.succAboveCases m ?_ ?_ i
          · rwa [Fin.insertNth_apply_same]
          · intro j; rw [Fin.insertNth_apply_succAbove]; exact hP j
        · rw [insertNth_sum]; exact hsum
    by_cases hc : t 0 ∈ Set.Icc (0 : ℝ) (1 - ∑ j, y j)
    · have hmem : (y, t) ∈ finIsolateEquivProd ℝ m '' (𝓡 (n + 1)) :=
        (mem_image_R_iff m (y, t)).mpr (hRiff.mpr ⟨hc.1, by linarith [hc.2]⟩)
      rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hc, hval]
    · have hnmem : (y, t) ∉ finIsolateEquivProd ℝ m '' (𝓡 (n + 1)) := by
        rw [mem_image_R_iff]
        exact fun hR ↦ hc ⟨(hRiff.mp hR).1, by linarith [(hRiff.mp hR).2]⟩
      rw [Set.indicator_of_notMem hnmem, Set.indicator_of_notMem hc]
  simp_rw [hint]
  rw [integral_ES1 (fun s ↦ (Set.Icc (0 : ℝ) (1 - ∑ j, y j)).indicator
        (fun s ↦ F (m.insertNth s (fun j ↦ y j))) s),
    MeasureTheory.integral_indicator measurableSet_Icc]

/-- At a non-admissible point (some coordinate negative), the inner marginal vanishes. -/
theorem inner_zero (n : ℕ) (m : Fin (n + 1)) (F : (Fin (n + 1) → ℝ) → ℝ)
    (y : EuclideanSpace ℝ (Fin (n + 1 - 1))) (hnP : ¬ ∀ j, 0 ≤ y j) :
    (∫ t : EuclideanSpace ℝ (Fin 1), (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z).ofLp) (y, t)) = 0 := by
  have h0 : ∀ t : EuclideanSpace ℝ (Fin 1), (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))).indicator
        (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z).ofLp) (y, t) = 0 := by
    intro t
    rw [Set.indicator_of_notMem]
    rw [mem_image_R_iff, symm_finIsolate_apply, EuclideanSpace.mem_scaledStdSimplex_iff]
    rintro ⟨hall, -⟩
    apply hnP
    intro j
    have := hall (m.succAbove j)
    rwa [WithLp.ofLp_toLp, Fin.insertNth_apply_succAbove] at this
  simp only [h0, integral_zero]

/-- The marginal of a `toLp` witness equals the squared iterated integral over `𝓡 n` and the
admissible coordinate interval. -/
theorem J_toLp_eq_iterated (n : ℕ) (m : Fin (n + 1)) (G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hmem : MemLp G 2 (volume.restrict (𝓡 (n + 1)))) :
    PrimeGaps.J m (hmem.toLp _) = ∫ t in 𝓡 (n + 1 - 1),
          (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i), G (insertLp m s t)) ^ 2 := by
  set F : (Fin (n + 1) → ℝ) → ℝ := fun x ↦ G (WithLp.toLp 2 x) with hFdef
  have hpoint : ∀ y : EuclideanSpace ℝ (Fin (n + 1 - 1)), (∫ t : EuclideanSpace ℝ (Fin 1),
          (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))).indicator
            (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z).ofLp) (y, t)) ^ 2 =
        (𝓡 (n + 1 - 1)).indicator
            (fun t ↦ (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i), G (insertLp m s t)) ^ 2) y := by
    intro y
    by_cases hP : ∀ j, 0 ≤ y j
    · rw [inner_pointwise n m F y hP]
      by_cases hsum : ∑ i, y i ≤ 1
      · have hymem : y ∈ 𝓡 (n + 1 - 1) := by
          exact ⟨hP, hsum⟩
        rw [Set.indicator_of_mem hymem]
        congr 1
      · have hnot : y ∉ 𝓡 (n + 1 - 1) := by
          intro h; exact hsum h.2
        rw [Set.indicator_of_notMem hnot, Set.Icc_eq_empty (by linarith [not_le.mp hsum])]
        simp
    · rw [inner_zero n m F y hP]
      have hnot : y ∉ 𝓡 (n + 1 - 1) := by
        intro h; exact hP h.1
      rw [Set.indicator_of_notMem hnot]
      simp
  have hmeas : MeasurableSet (𝓡 (n + 1 - 1)) :=
    (EuclideanSpace.isClosed_scaledStdSimplex (k := n) (s := 1)).measurableSet
  rw [J_marginal_toLp]
  have hidx : (fun z : EuclideanSpace ℝ (Fin (n + 1 - 1)) × EuclideanSpace ℝ (Fin 1) ↦
        G ((finIsolateEquivProd ℝ m).symm z)) =
      (fun z ↦ F ((finIsolateEquivProd ℝ m).symm z).ofLp) := by
    funext z
    simp only [hFdef, WithLp.toLp_ofLp]
  rw [hidx, ← MeasureTheory.integral_indicator hmeas]
  exact integral_congr_ae (Filter.Eventually.of_forall hpoint)

end PrimeGaps
