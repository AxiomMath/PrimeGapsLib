/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Variational.EnlargedSimplex
public import PrimeGapsTheory.Variational.MkVerified

/-!
# Enlarged marginal quadratic forms

This module defines the ε-shrunken marginal `jEps`, its Rayleigh quotient `qEps`, and
their continuous quadratic-form realizations on the enlarged simplex.

## Main definitions

* `jEps`: The ε-shrunken marginal quadratic form.
* `qEps`: The enlarged Rayleigh quotient.
* `enlargedJQF`: The intrinsic marginal quadratic form on `LÂ²`.
-/

@[expose] public section

open scoped InnerProductSpace

open MeasureTheory
open EuclideanSpace
open scoped PrimeGaps
open PrimeGaps

namespace Gaps246

theorem measurableSet_shrunkenSlice (k : ℕ) (ε : ℝ) : MeasurableSet (shrunkenSlice k ε) := by
  unfold shrunkenSlice
  have hproj : ∀ i, Measurable (fun x : EuclideanSpace ℝ (Fin (k - 1)) ↦ x i) :=
    fun i ↦ (EuclideanSpace.proj i).continuous.measurable
  have hcoord : MeasurableSet {x : EuclideanSpace ℝ (Fin (k - 1)) | ∀ i, 0 ≤ x i} := by
    have heq : {x : EuclideanSpace ℝ (Fin (k - 1)) | ∀ i, 0 ≤ x i} =
        ⋂ i, {x : EuclideanSpace ℝ (Fin (k - 1)) | 0 ≤ x i} := by
      ext x
      simp
    rw [heq]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (hproj i)
  have hsum : MeasurableSet {x : EuclideanSpace ℝ (Fin (k - 1)) | ∑ i, x i ≤ 1 - ε} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ ↦ hproj i) measurable_const
  exact hcoord.inter hsum

/-- Reconstruct a point of `ES(ℝ, k)` from a value `s` at coordinate `i` and the
remaining `k-1` coordinates `t`.  This is the `Fin.insertNth`-style splice used to
express the marginal integral; it is written index-by-index so that it typechecks
for a fully generic `k` (`Fin.insertNth` would require `k` to appear syntactically
as a successor). -/
noncomputable def sliceInsert (k : ℕ) (i : Fin k) (s : ℝ) (t : Fin (k - 1) → ℝ) : Fin k → ℝ :=
  fun j ↦
    if h : (j : ℕ) < (i : ℕ) then t ⟨j, by have := i.2; omega⟩
    else if h2 : (j : ℕ) = (i : ℕ) then s
    else t ⟨(j : ℕ) - 1, by have := j.2; omega⟩

/-- The slice-insertion `sliceInsert` agrees with `Fin.insertNth`: reconstructing a
point by splicing `s` at coordinate `i` is the standard `insertNth`.  (The original
`sliceInsert` is written index-by-index so it typechecks at a generic `k`; here we
identify it with the library map on the successor shape `k = n+1`.) -/
theorem sliceInsert_eq_insertNth {n : ℕ} (i : Fin (n + 1)) (s : ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    sliceInsert (n + 1) i s (fun j ↦ t j) = i.insertNth s (fun j ↦ t j) := by
  funext j
  refine Fin.succAboveCases i ?_ ?_ j
  · -- j = i: `sliceInsert` picks the `= i` branch, `insertNth` gives `s`.
    simp only [sliceInsert, Fin.insertNth_apply_same, lt_irrefl, dif_neg,
      not_false_eq_true, dif_pos]
  · -- j = i.succAbove k: `insertNth` gives `t k`; `sliceInsert` also picks `t k`.
    intro k
    rw [Fin.insertNth_apply_succAbove]
    simp only [sliceInsert]
    rcases lt_or_ge (k : ℕ) (i : ℕ) with hk | hk
    · -- below the insertion point: `succAbove` is `castSucc`, index unchanged.
      have hji : ((i.succAbove k : Fin (n + 1)) : ℕ) = (k : ℕ) := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by exact_mod_cast hk)]; rfl
      rw [dif_pos (by omega)]
      exact congrArg (fun idx : Fin n ↦ t idx) (Fin.ext hji)
    · -- at or above: `succAbove` is `succ`, index is `k+1`, minus one is `k`.
      have hji : ((i.succAbove k : Fin (n + 1)) : ℕ) = (k : ℕ) + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by exact_mod_cast hk)]; rfl
      have hidx : ((i.succAbove k : Fin (n + 1)) : ℕ) - 1 = (k : ℕ) := by omega
      rw [dif_neg (by omega), dif_neg (by omega)]
      exact congrArg (fun idx : Fin n ↦ t idx) (Fin.ext hidx)

/-- **`def_j_eps`.** The ε-shrunken marginal `J^{(i)}_ε(F)`:
`∫_{𝒮_ε} (∫₀^∞ F(insert t_i) dt_i)² dt_{ĩ}`.  The inner integral runs the `i`-th
coordinate over `[0, ∞)`; the outer integral runs the remaining `k-1` coordinates
over the shrunken slice `𝒮_ε`.  Mirrors the shape of `lem_quad_forms`. -/
noncomputable def jEps (k : ℕ) (ε : ℝ) (i : Fin k) (F : EuclideanSpace ℝ (Fin k) → ℝ) : ℝ :=
  ∫ t in shrunkenSlice k ε, (∫ s in Set.Ici (0 : ℝ), F (WithLp.toLp 2 (sliceInsert k i s t))) ^ 2

/-- **`def_q`.** The enlarged witness ratio
`𝒬_ε(F) = (∑ᵢ J^{(i)}_ε(F)) / ∫_{𝒯_ε} F²`.

This is deliberately a functional of a concrete function, rather than of an `L²`
equivalence class on the standard simplex.  The marginal samples `F` throughout the
enlarged simplex, so quotienting only modulo a.e. equality on `𝓡 k` would not define it. -/
noncomputable def qEps (k : ℕ) (ε : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ) : ℝ :=
  (∑ i, jEps k ε i F) / (∫ x in enlargedSimplex k ε, (F x) ^ 2)

/-!
## The enlarged marginal as a continuous `L²` operator

The concrete definition `jEps` is the form used by the sieve and certificate.
For approximation arguments we also need its intrinsic `L²` realization.  First
integrate an `L²(𝒯_ε)` function in coordinate `i`, then restrict the resulting
function of the other coordinates to the shrunken slice `𝒮_ε`.  Both operations
are continuous linear maps; taking the squared norm therefore gives a continuous
quadratic form.  The representative theorem below identifies this construction
with `jEps`.
-/

/-- The `L²` space on the enlarged simplex. -/
noncomputable abbrev EnlargedLp (k : ℕ) (ε : ℝ) := Lp ℝ 2 (volume.restrict (enlargedSimplex k ε))

/-- Partial integration followed by restriction to the shrunken slice. -/
noncomputable def enlargedMarginalCLM {k : ℕ} (ε : ℝ) (i : Fin k) :
    EnlargedLp k ε →L[ℝ] Lp ℝ 2 (volume.restrict (shrunkenSlice k ε)) :=
  (LpToLpRestrictCLM (EuclideanSpace ℝ (Fin (k - 1))) ℝ ℝ volume 2 (shrunkenSlice k ε)).comp
    (Lp.integralVarCLM i (isClosed_enlargedSimplex k ε).measurableSet
      (.of_isCompact (isCompact_enlargedSimplex k ε)))

/-- The intrinsic enlarged marginal quadratic form on `L²(𝒯_ε)`. -/
noncomputable def enlargedJQF {k : ℕ} (ε : ℝ) (i : Fin k) : QuadraticForm ℝ (EnlargedLp k ε) :=
  ((innerSL ℝ).bilinearComp (enlargedMarginalCLM ε i)
    (enlargedMarginalCLM ε i)).toBilinForm.toQuadraticMap

/-- The draft enlarged marginal is the shared `JEps` operator. -/
theorem enlargedJQF_eq_JEps {k : ℕ} (ε : ℝ) (i : Fin k) :
    enlargedJQF ε i = PrimeGaps.JEps ε i := rfl

theorem enlargedJQF_apply {k : ℕ} (ε : ℝ) (i : Fin k) (f : EnlargedLp k ε) :
    enlargedJQF ε i f = ‖enlargedMarginalCLM ε i f‖ ^ 2 := by
  rw [enlargedJQF]
  simp [ContinuousLinearMap.bilinearComp_apply]

@[fun_prop]
theorem continuous_enlargedJQF {k : ℕ} (ε : ℝ) (i : Fin k) : Continuous (enlargedJQF ε i) := by
  have hqf : (enlargedJQF ε i : EnlargedLp k ε → ℝ) = fun f ↦ ‖enlargedMarginalCLM ε i f‖ ^ 2 := by
    funext f
    exact enlargedJQF_apply ε i f
  rw [hqf]
  fun_prop

/-- Iterated-integral formula for the intrinsic enlarged marginal, with an
honest concrete representative in the integrand. -/
theorem enlargedJQF_marginal_toLp {k : ℕ} (ε : ℝ) (i : Fin k) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : MemLp F 2 (volume.restrict (enlargedSimplex k ε))) :
    enlargedJQF ε i (hF.toLp F) =
      ∫ y in shrunkenSlice k ε,
        (∫ t : EuclideanSpace ℝ (Fin 1),
            (finIsolateEquivProd ℝ i '' enlargedSimplex k ε).indicator
              (fun z ↦ F ((finIsolateEquivProd ℝ i).symm z)) (y, t) ∂volume) ^ 2 ∂volume := by
  let S := enlargedSimplex k ε
  have hMS : MeasurableSet S := (isClosed_enlargedSimplex k ε).measurableSet
  have hES : EssFiniteSnd (finIsolateEquivProd ℝ i '' S) volume volume :=
    .of_isCompact (isCompact_enlargedSimplex k ε)
  have himg : MeasurableSet (finIsolateEquivProd ℝ i '' S) :=
    (finIsolateEquivProd ℝ i).toHomeomorph.measurableEmbedding.measurableSet_image.mpr hMS
  have hmp :
      MeasurePreserving (finIsolateEquivProd ℝ i).symm
        (volume.restrict (finIsolateEquivProd ℝ i '' S)) (volume.restrict S) := by
    have h := (measurePreserving_symm_finIsolateEquivProd i).restrict_preimage hMS
    rwa [← (finIsolateEquivProd ℝ i).image_eq_preimage_symm] at h
  have hrep :
      (finIsolateEquivProd ℝ i '' S).indicator (fun z ↦ (hF.toLp F : EuclideanSpace ℝ (Fin k) → ℝ)
            ((finIsolateEquivProd ℝ i).symm z)) =ᵐ[volume]
        (finIsolateEquivProd ℝ i '' S).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ i).symm z)) := by
    have hae :
        (fun z ↦ (hF.toLp F : EuclideanSpace ℝ (Fin k) → ℝ)
            ((finIsolateEquivProd ℝ i).symm z)) =ᵐ[volume.restrict (finIsolateEquivProd ℝ i '' S)]
          fun z ↦ F ((finIsolateEquivProd ℝ i).symm z) :=
      hmp.quasiMeasurePreserving.ae_eq_comp hF.coeFn_toLp
    filter_upwards [(ae_restrict_iff' himg).mp hae] with z hz
    by_cases hzS : z ∈ finIsolateEquivProd ℝ i '' S
    · simp [Set.indicator_of_mem hzS, hz hzS]
    · simp [Set.indicator_of_notMem hzS]
  rw [enlargedJQF_apply, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  have hrestrict := LpToLpRestrictCLM_coeFn ℝ (shrunkenSlice k ε)
    (Lp.integralVarCLM i hMS hES (hF.toLp F))
  have hvar := PrimeGaps.coeFn_integralVarCLM i hMS hES (hF.toLp F)
  filter_upwards [hrestrict, ae_restrict_of_ae hvar,
    ae_restrict_of_ae (Measure.ae_ae_of_ae_prod hrep)] with y hyr hyv hyrep
  change ⟪((LpToLpRestrictCLM
        (EuclideanSpace ℝ (Fin (k - 1))) ℝ ℝ volume 2 (shrunkenSlice k ε))
        (Lp.integralVarCLM i hMS hES (hF.toLp F)) y),
      ((LpToLpRestrictCLM
          (EuclideanSpace ℝ (Fin (k - 1))) ℝ ℝ volume 2 (shrunkenSlice k ε))
        (Lp.integralVarCLM i hMS hES (hF.toLp F)) y)⟫_ℝ = _
  rw [hyr, hyv, integral_congr_ae hyrep]
  simp [sq, S]

/-- For an honest representative that vanishes off the enlarged simplex, the
intrinsic quadratic form is exactly the concrete shrunken marginal `jEps`. -/
theorem enlargedJQF_toLp_eq_jEps {n : ℕ} (ε : ℝ) (i : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : MemLp F 2 (volume.restrict (enlargedSimplex (n + 1) ε)))
    (hsupp : ∀ x, x ∉ enlargedSimplex (n + 1) ε → F x = 0) :
    enlargedJQF ε i (hF.toLp F) = jEps (n + 1) ε i F := by
  rw [enlargedJQF_marginal_toLp ε i F hF, jEps]
  refine setIntegral_congr_fun ?_ fun y _ ↦ ?_
  · exact measurableSet_shrunkenSlice (n + 1) ε
  congr 1
  let G : ℝ → ℝ := fun s ↦
    (finIsolateEquivProd ℝ i '' enlargedSimplex (n + 1) ε).indicator
      (fun z ↦ F ((finIsolateEquivProd ℝ i).symm z))
      (y, WithLp.toLp 2 (fun _ ↦ s))
  have hinner :
      (∫ t : EuclideanSpace ℝ (Fin 1),
          (finIsolateEquivProd ℝ i '' enlargedSimplex (n + 1) ε).indicator
            (fun z ↦ F ((finIsolateEquivProd ℝ i).symm z)) (y, t) ∂volume) = ∫ s : ℝ, G s :=
    calc _
        = ∫ t : EuclideanSpace ℝ (Fin 1), G (t 0) ∂volume := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun t ↦ ?_)
          unfold G
          congr 3
          ext j
          exact congrArg (fun q ↦ t q) (Subsingleton.elim j 0)
      _ = ∫ s : ℝ, G s := PrimeGaps.integral_ES1 G
  rw [hinner, ← MeasureTheory.integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Filter.Eventually.of_forall fun s ↦ ?_)
  let t : EuclideanSpace ℝ (Fin 1) := WithLp.toLp 2 (fun _ ↦ s)
  let x : EuclideanSpace ℝ (Fin (n + 1)) := (finIsolateEquivProd ℝ i).symm (y, t)
  have hx : x = WithLp.toLp 2 (sliceInsert (n + 1) i s fun j ↦ y j) := by
    have hsymm : x = WithLp.toLp 2 (i.insertNth (t 0) (fun j ↦ y j)) :=
      PrimeGaps.symm_finIsolate_apply n i y t
    have ht0 : t 0 = s := by simp [t]
    rw [hsymm, ht0, sliceInsert_eq_insertNth i s y]
  have himg : (y, t) ∈ finIsolateEquivProd ℝ i '' enlargedSimplex (n + 1) ε ↔
        x ∈ enlargedSimplex (n + 1) ε := by
    constructor
    · rintro ⟨z, hz, hzi⟩
      have hxdef : x = (finIsolateEquivProd ℝ i).symm (y, t) := rfl
      have : z = x := by
        rw [hxdef, ← hzi]
        exact (finIsolateEquivProd ℝ i).symm_apply_apply z |>.symm
      rwa [← this]
    · intro hxmem
      exact ⟨x, hxmem, (finIsolateEquivProd ℝ i).apply_symm_apply (y, t)⟩
  by_cases hs : 0 ≤ s
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr hs)]
    by_cases hxin : x ∈ enlargedSimplex (n + 1) ε
    · have hG : G s = F x := by
        change (finIsolateEquivProd ℝ i '' enlargedSimplex (n + 1) ε).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ i).symm z)) (y, t) = F x
        rw [Set.indicator_of_mem (himg.mpr hxin)]
      rw [hG, hx]
    · have hG : G s = 0 := by
        change (finIsolateEquivProd ℝ i '' enlargedSimplex (n + 1) ε).indicator
          (fun z ↦ F ((finIsolateEquivProd ℝ i).symm z)) (y, t) = 0
        rw [Set.indicator_of_notMem (not_congr himg |>.mpr hxin)]
      rw [hG, ← hx]
      exact (hsupp x hxin).symm
  · have hxout : x ∉ enlargedSimplex (n + 1) ε := by
      intro hxin
      have hnonneg := hxin.1 i
      rw [hx] at hnonneg
      simp only [sliceInsert, lt_irrefl, dif_pos] at hnonneg
      exact hs hnonneg
    have hG : G s = 0 := by
      change (finIsolateEquivProd ℝ i '' enlargedSimplex (n + 1) ε).indicator
        (fun z ↦ F ((finIsolateEquivProd ℝ i).symm z)) (y, t) = 0
      rw [Set.indicator_of_notMem (not_congr himg |>.mpr hxout)]
    rw [hG, Set.indicator_of_notMem (by simpa [Set.mem_Ici] using hs)]

/-- The numerator of the enlarged Rayleigh quotient, intrinsically on `L²`. -/
noncomputable def enlargedNumerator {k : ℕ} (ε : ℝ) (f : EnlargedLp k ε) : ℝ :=
  ∑ i, enlargedJQF ε i f

theorem continuous_enlargedNumerator {k : ℕ} (ε : ℝ) :
    Continuous (enlargedNumerator ε : EnlargedLp k ε → ℝ) :=
  continuous_finsetSum _ fun i _ ↦ continuous_enlargedJQF ε i

theorem enlargedNumerator_toLp {n : ℕ} (ε : ℝ) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : MemLp F 2 (volume.restrict (enlargedSimplex (n + 1) ε)))
    (hsupp : ∀ x, x ∉ enlargedSimplex (n + 1) ε → F x = 0) :
    enlargedNumerator ε (hF.toLp F) = ∑ i, jEps (n + 1) ε i F := by
  unfold enlargedNumerator
  exact Finset.sum_congr rfl fun i _ ↦ enlargedJQF_toLp_eq_jEps ε i F hF hsupp

/-- The denominator of the enlarged Rayleigh quotient, intrinsically on `L²`. -/
noncomputable def enlargedDenominator {k : ℕ} {ε : ℝ} (f : EnlargedLp k ε) : ℝ := ‖f‖ ^ 2

theorem continuous_enlargedDenominator {k : ℕ} {ε : ℝ} :
    Continuous (enlargedDenominator : EnlargedLp k ε → ℝ) := by
  unfold enlargedDenominator
  fun_prop

/-- Concrete integral formula for the intrinsic denominator. -/
theorem enlargedDenominator_toLp {k : ℕ} {ε : ℝ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : MemLp F 2 (volume.restrict (enlargedSimplex k ε))) :
    enlargedDenominator (hF.toLp F) = ∫ x in enlargedSimplex k ε, (F x) ^ 2 := by
  rw [enlargedDenominator, ← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hF.coeFn_toLp] with x hx
  rw [hx]
  simp [sq]

/-- The intrinsic enlarged Rayleigh quotient. -/
noncomputable def enlargedRayleigh {k : ℕ} (ε : ℝ) (f : EnlargedLp k ε) : ℝ :=
  enlargedNumerator ε f / enlargedDenominator f

theorem enlargedRayleigh_eq_shared {k : ℕ} (ε : ℝ) (f : EnlargedLp k ε) :
    enlargedRayleigh ε f = (∑ m, PrimeGaps.JEps ε m f) / ‖f‖ ^ 2 := by
  rw [enlargedRayleigh, enlargedNumerator, enlargedDenominator]
  simp_rw [enlargedJQF_eq_JEps]
  congr 2

theorem continuousAt_enlargedRayleigh {k : ℕ} (ε : ℝ)
    (f : EnlargedLp k ε) (hf : enlargedDenominator f ≠ 0) :
    ContinuousAt (enlargedRayleigh ε) f :=
  (continuous_enlargedNumerator ε).continuousAt.div
    continuous_enlargedDenominator.continuousAt hf

theorem enlargedRayleigh_toLp_eq_qEps {n : ℕ} (ε : ℝ) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : MemLp F 2 (volume.restrict (enlargedSimplex (n + 1) ε)))
    (hsupp : ∀ x, x ∉ enlargedSimplex (n + 1) ε → F x = 0) :
    enlargedRayleigh ε (hF.toLp F) = qEps (n + 1) ε F := by
  rw [enlargedRayleigh, qEps, enlargedNumerator_toLp ε F hF hsupp, enlargedDenominator_toLp F hF]

theorem dist_toLp_toLp_eq_eLpNorm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} (F G : α → ℝ) (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    dist (hF.toLp F) (hG.toLp G) = (eLpNorm (fun x ↦ F x - G x) 2 μ).toReal := by
  rw [Lp.dist_def]
  refine congrArg ENNReal.toReal (eLpNorm_congr_ae ?_)
  filter_upwards [hF.coeFn_toLp, hG.coeFn_toLp] with x hxF hxG
  simp [hxF, hxG]

/-- **Recovery (`ε = 0`).** For a genuine function `G` that is square-integrable on the
simplex and **vanishes off `𝓡 (n+1)`**, the shrunken marginal `jEps (n+1) 0 i G` equals
the 600 marginal `PrimeGaps.J i (G.toLp)`.  The support hypothesis is essential: `jEps`
integrates the inner coordinate over `[0, ∞)`, so without `G` vanishing beyond the
simplex face the unbounded tail does not match `PrimeGaps.J`'s truncated `[0, 1-∑t]`
integral.  (The earlier `⇑F`-form was *false* precisely because the `Lp` representative
is unconstrained off the null simplex complement.) -/
theorem jEps_zero {n : ℕ} (i : Fin (n + 1)) (G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hmem : MemLp G 2 (volume.restrict (𝓡 (n + 1))))
    (hsupp : ∀ x, x ∉ 𝓡 (n + 1) → G x = 0) :
    jEps (n + 1) 0 i G = PrimeGaps.J i (hmem.toLp G) := by
  rw [PrimeGaps.J_toLp_eq_iterated n i G hmem, jEps, shrunkenSlice_zero]
  refine setIntegral_congr_fun isClosed_scaledStdSimplex.measurableSet (fun t ht ↦ ?_)
  have htmem := ht
  obtain ⟨htnn, htsum⟩ := htmem
  congr 1
  have hins : ∀ s : ℝ, G (WithLp.toLp 2 (sliceInsert (n + 1) i s t)) = G (insertLp i s t) := by
    intro s
    congr 1
    rw [insertLp, sliceInsert_eq_insertNth i s t]
  simp_rw [hins]
  have hvanish : ∀ s ∈ Set.Ioi (1 - ∑ j, t j), G (insertLp i s t) = 0 := by
    intro s hs
    apply hsupp
    rw [EuclideanSpace.mem_scaledStdSimplex_iff]
    rintro ⟨ - , hsum⟩
    rw [insertLp, WithLp.ofLp_toLp, insertNth_sum] at hsum
    simp only [Set.mem_Ioi] at hs
    have hsum' : s + ∑ j, t j ≤ 1 := hsum
    linarith [hs]
  rw [← MeasureTheory.integral_indicator measurableSet_Ici,
    ← MeasureTheory.integral_indicator measurableSet_Icc]
  refine congrArg _ (funext fun s ↦ ?_)
  by_cases hIcc : s ∈ Set.Icc (0 : ℝ) (1 - ∑ j, t j)
  · rw [Set.indicator_of_mem hIcc, Set.indicator_of_mem (Set.mem_Ici.mpr hIcc.1)]
  · rw [Set.indicator_of_notMem hIcc]
    by_cases hIci : s ∈ Set.Ici (0 : ℝ)
    · rw [Set.indicator_of_mem hIci]
      simp only [Set.mem_Ici] at hIci
      simp only [Set.mem_Icc, not_and, not_le] at hIcc
      exact hvanish s (Set.mem_Ioi.mpr (hIcc hIci))
    · rw [Set.indicator_of_notMem hIci]

/-- **Recovery (`ε = 0`) for the witness ratio.** -/
theorem qEps_zero {n : ℕ} (G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hmem : MemLp G 2 (volume.restrict (𝓡 (n + 1))))
    (hsupp : ∀ x, x ∉ 𝓡 (n + 1) → G x = 0) :
    qEps (n + 1) 0 G = (∑ i, PrimeGaps.J i (hmem.toLp G)) / ‖hmem.toLp G‖ ^ 2 := by
  unfold qEps
  rw [enlargedSimplex_zero]
  congr 1
  · refine Finset.sum_congr rfl (fun i _ ↦ ?_)
    exact jEps_zero i G hmem hsupp
  · exact (PrimeGaps.I_toLp_eq (n + 1) G hmem).symm

end Gaps246
