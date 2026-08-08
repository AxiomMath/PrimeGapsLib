/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SieveDatumEval
public import PrimeGapsTheory.Variational.MkVerified
public import PrimeGapsTheory.Variational.PosDef

/-!
# The marginal profile `Tm`

Defines the coordinate marginal of a smooth simplex-supported profile and establishes its analytic
properties.

## Main definitions

*  `Tm`: The marginal obtained by integrating one inserted coordinate.

## Main results

*  `Tm_contDiff`: The marginal of a smooth simplex-supported profile is smooth.
*  `Tm_support`: The marginal is supported on the lower-dimensional simplex.
*  `Tm_abs_le_Fmax`: The marginal is bounded by the profile norm.
*  `Tm_sq_integral_eq_J`: The squared marginal integral equals the quadratic form `J`.
-/

@[expose] public section

open scoped Topology

namespace PrimeGaps

open Finset MeasureTheory EuclideanSpace
open scoped PrimeGaps Convolution

local notation "ES(" 𝕜 ", " k ")" => EuclideanSpace 𝕜 (Fin k)

variable {n : ℕ}

/-! ## Smooth retained profiles -/

/-- The normalized retained cutoff. -/
noncomputable def retainedCutoffScale (ε : ℝ) : ℝ := (1 - ε) / (1 + ε)

/-- A smooth approximation to the indicator that the coordinate sum away from `m` is below the
retained cutoff. -/
noncomputable def retainedRamp {k : ℕ} (ε η : ℝ) (m : Fin k) (x : EuclideanSpace ℝ (Fin k)) : ℝ :=
  Real.smoothTransition ((retainedCutoffScale ε - ∑ i ∈ Finset.univ.erase m, x i) / η)

/-- The product of a retained cutoff ramp and a base profile. -/
noncomputable def retainedProfile {k : ℕ} (ε η : ℝ) (m : Fin k) (G : EuclideanSpace ℝ (Fin k) → ℝ) :
    EuclideanSpace ℝ (Fin k) → ℝ :=
  fun x ↦ retainedRamp ε η m x * G x

/-- `0 ≤ retainedRamp ε η m x`. -/
theorem retainedRamp_nonneg {k : ℕ} (ε η : ℝ) (m : Fin k) (x : EuclideanSpace ℝ (Fin k)) :
    0 ≤ retainedRamp ε η m x :=
  Real.smoothTransition.nonneg _

/-- `retainedRamp ε η m x ≤ 1`. -/
theorem retainedRamp_le_one {k : ℕ} (ε η : ℝ) (m : Fin k) (x : EuclideanSpace ℝ (Fin k)) :
    retainedRamp ε η m x ≤ 1 :=
  Real.smoothTransition.le_one _

/-- The ramp vanishes once `∑_{i ≠ m} xᵢ` reaches the cutoff `retainedCutoffScale ε`. -/
theorem retainedRamp_eq_zero_of_boundary {k : ℕ} {ε η : ℝ}
    (hη : 0 < η) (m : Fin k) (x : EuclideanSpace ℝ (Fin k))
    (hx : retainedCutoffScale ε ≤ ∑ i ∈ Finset.univ.erase m, x i) :
    retainedRamp ε η m x = 0 := by
  unfold retainedRamp
  apply Real.smoothTransition.zero_of_nonpos
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hx) hη.le

/-- The retained ramps at reciprocal natural widths converge to the strict cutoff indicator. -/
theorem retainedRamp_inv_succ_tendsto {k : ℕ} (ε : ℝ) (m : Fin k) (x : EuclideanSpace ℝ (Fin k)) :
    Filter.Tendsto (fun n : ℕ ↦ retainedRamp ε (((n + 1 : ℕ) : ℝ)⁻¹) m x)
      Filter.atTop
      (𝓝 (if (∑ i ∈ Finset.univ.erase m, x i) < retainedCutoffScale ε then 1 else 0)) := by
  by_cases hx : (∑ i ∈ Finset.univ.erase m, x i) < retainedCutoffScale ε
  · rw [if_pos hx]
    let a : ℝ := retainedCutoffScale ε - ∑ i ∈ Finset.univ.erase m, x i
    have ha : 0 < a := sub_pos.mpr hx
    obtain ⟨N : ℕ, hN⟩ := exists_nat_gt (1 / a)
    have hev : ∀ᶠ n : ℕ in Filter.atTop, 1 ≤ a * ((n + 1 : ℕ) : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hainv : a * (1 / a) = 1 := by field_simp
      have hn1 : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ n
      have hdiv : 1 / a < ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le hN (hcast.trans hn1)
      have hmul := mul_lt_mul_of_pos_left hdiv ha
      rw [hainv] at hmul
      exact hmul.le
    apply Filter.Tendsto.congr' _
      (show Filter.Tendsto (fun _ : ℕ ↦ (1 : ℝ)) Filter.atTop (𝓝 1) from tendsto_const_nhds)
    filter_upwards [hev] with n hn
    symm
    unfold retainedRamp
    rw [Real.smoothTransition.one_of_one_le]
    simpa [a, div_eq_mul_inv] using hn
  · rw [if_neg hx]
    apply Filter.Tendsto.congr' _
      (show Filter.Tendsto (fun _ : ℕ ↦ (0 : ℝ)) Filter.atTop (𝓝 0) from tendsto_const_nhds)
    filter_upwards with n
    symm
    exact retainedRamp_eq_zero_of_boundary
      (inv_pos.mpr (by positivity : (0 : ℝ) < ((n + 1 : ℕ) : ℝ)))
      m x (le_of_not_gt hx)

/-- The retained ramp is independent of the distinguished inserted coordinate. -/
theorem retainedRamp_insertLp {n : ℕ} (ε η : ℝ)
    (m : Fin (n + 1)) (s s' : ℝ) (t : EuclideanSpace ℝ (Fin n)) :
    retainedRamp ε η m (EuclideanSpace.insertLp m s t) =
      retainedRamp ε η m (EuclideanSpace.insertLp m s' t) := by
  unfold retainedRamp
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  cases i using Fin.succAboveCases m
  · simp at hi
  · simp [EuclideanSpace.insertLp_apply_succAbove]

/-- The retained profile of a smooth `G` is smooth. -/
theorem retainedProfile_contDiff {k : ℕ} {ε η : ℝ} (m : Fin k)
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (retainedProfile ε η m G) := by
  unfold retainedProfile retainedRamp retainedCutoffScale
  fun_prop

/-- The retained profile inherits the simplex support of `G`. -/
theorem retainedProfile_support {k : ℕ} {ε η : ℝ} (m : Fin k)
    {G : EuclideanSpace ℝ (Fin k) → ℝ} (hG : Function.support G ⊆ 𝓡 k) :
    Function.support (retainedProfile ε η m G) ⊆ 𝓡 k := by
  intro x hx
  apply hG
  exact fun hzero ↦ hx (by simp [retainedProfile, hzero])

/-- The `L²` representative of a smooth retained profile supported on the simplex. -/
noncomputable def retainedProfileLp {k : ℕ} {ε η : ℝ} (m : Fin k) (G : EuclideanSpace ℝ (Fin k) → ℝ)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGsupp : Function.support G ⊆ 𝓡 k) :
    Lp ℝ 2 (volume.restrict (𝓡 k)) :=
  ((retainedProfile_contDiff m hG).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        isCompact_scaledStdSimplex
        (retainedProfile_support m hGsupp))).toLp
    (retainedProfile ε η m G)

/-- The `m` -th marginal of `F` as a function on `ES(ℝ, n)`, integrating the inserted coordinate
over the whole real line. -/
noncomputable def Tm (m : Fin (n + 1)) (F : ES(ℝ, n + 1) → ℝ) (t : ES(ℝ, n)) : ℝ :=
  ∫ (s : ℝ), F (insertLp m s t)

/-- `(p: ES × ℝ) ↦ insertLp m (-p.2) p.1` is `C^∞` (continuous-linear reassembly). -/
theorem contDiff_insertLp_neg (m : Fin (n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (fun p : ES(ℝ, n) × ℝ ↦ insertLp m (-p.2) p.1) := by
  rw [contDiff_euclidean]
  intro i
  refine Fin.succAboveCases m ?_ ?_ i
  · simp_rw [insertLp_apply_same]
    exact contDiff_snd.neg
  · intro j
    simp_rw [insertLp_apply_succAbove]
    exact ((contDiff_euclidean.mp contDiff_id) j).comp contDiff_fst

/-- `Tm m F` is `C^∞`. -/
theorem Tm_contDiff (m : Fin (n + 1)) (F : ES(ℝ, n + 1) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1)) :
    ContDiff ℝ (⊤ : ℕ∞) (Tm m F) := by
  classical
  set g : ES(ℝ, n) → ℝ → ℝ := fun t s ↦ F (insertLp m (-s) t) with hg
  set f : ℝ → ℝ := fun _ ↦ (1 : ℝ) with hf
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ with hL
  have hconv : Tm m F = fun t : ES(ℝ, n) ↦ (f ⋆[L, volume] g t) 0 := by
    funext t
    rw [Tm, convolution_def]
    apply integral_congr_ae
    filter_upwards with y
    simp [hf, hg, hL, ContinuousLinearMap.lsmul_apply]
  rw [hconv, ← contDiffOn_univ]
  refine contDiffOn_convolution_right_with_param_comp (v := fun _ ↦ (0 : ℝ))
    L contDiffOn_const isOpen_univ (isCompact_Icc (a := (-1 : ℝ)) (b := 1)) ?_ ?_ ?_
  · intro t x _ hx
    simp only [hg]
    have hxout : (-x) ∉ Set.Icc (0 : ℝ) 1 := by
      rw [Set.mem_Icc] at hx ⊢
      exact fun h ↦ hx ⟨by linarith [h.2], by linarith [h.1]⟩
    have hnot : insertLp m (-x) t ∉ 𝓡 (n + 1) := by
      rw [EuclideanSpace.mem_scaledStdSimplex_iff]
      rintro ⟨hnn, hsum⟩
      apply hxout
      constructor
      · have := hnn m; rwa [insertLp_apply_same] at this
      · have hm := hnn m
        rw [insertLp_apply_same] at hm
        have : (insertLp m (-x) t) m ≤ ∑ i, (insertLp m (-x) t) i := by
          apply Finset.single_le_sum (fun i _ ↦ hnn i) (Finset.mem_univ m)
        rw [insertLp_apply_same] at this
        linarith
    by_contra hne
    exact hnot (hsupp hne)
  · exact (locallyIntegrable_const (1 : ℝ))
  · have hcomp : ContDiff ℝ (⊤ : ℕ∞) (fun p : ES(ℝ, n) × ℝ ↦ F (insertLp m (-p.2) p.1)) :=
      hF.comp (contDiff_insertLp_neg m)
    exact (hcomp.contDiffOn)

/-- If `insertLp m s t ∈ 𝓡 (n+1)` then the inserted value and base point satisfy the simplex
bounds. -/
theorem insertLp_mem_R_bounds (m : Fin (n + 1)) (s : ℝ) (t : ES(ℝ, n))
    (h : insertLp m s t ∈ 𝓡 (n + 1)) :
    0 ≤ s ∧ s + ∑ i, t i ≤ 1 ∧ ∀ j, 0 ≤ t j := by
  rw [EuclideanSpace.mem_scaledStdSimplex_iff] at h
  obtain ⟨hnn, hsum⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have := hnn m; rwa [insertLp_apply_same] at this
  · rwa [sum_insertLp] at hsum
  · intro j; have := hnn (m.succAbove j); rwa [insertLp_apply_succAbove] at this

/-- The integrand `s ↦ F (insertLp m s t)` vanishes outside `[0, 1 - ∑ t]`. -/
theorem F_insertLp_zero_of_notin_Icc (m : Fin (n + 1)) (F : ES(ℝ, n + 1) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (t : ES(ℝ, n)) {s : ℝ}
    (hs : s ∉ Set.Icc (0 : ℝ) (1 - ∑ i, t i)) :
    F (insertLp m s t) = 0 := by
  by_contra hne
  have hmem : insertLp m s t ∈ 𝓡 (n + 1) := hsupp hne
  obtain ⟨hs0, hsum, -⟩ := insertLp_mem_R_bounds m s t hmem
  exact hs ⟨hs0, by linarith⟩

/-- `Tm m F t = ∫_{[0,1-∑t]} F (insertLp m s t) ds`. -/
theorem Tm_eq_Icc (m : Fin (n + 1)) (F : ES(ℝ, n + 1) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (t : ES(ℝ, n)) :
    Tm m F t = ∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i), F (insertLp m s t) := by
  rw [Tm, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  exact fun s hs ↦ F_insertLp_zero_of_notin_Icc m F hsupp t hs

/-- `Tm` agrees with the raw-pi `PrimeGaps.marginal` of the `toLp` -precomposed profile. -/
theorem Tm_eq_marginal (m : Fin (n + 1)) (F : ES(ℝ, n + 1) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) (t : ES(ℝ, n)) :
    Tm m F t = PrimeGaps.marginal m (fun x ↦ F (WithLp.toLp 2 x)) t := by
  rw [Tm_eq_Icc m F hsupp t, PrimeGaps.marginal]; rfl

/-- `Function.support (Tm m F) ⊆ 𝓡 n`. -/
theorem Tm_support (m : Fin (n + 1)) (F : ES(ℝ, n + 1) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 (n + 1)) :
    Function.support (Tm m F) ⊆ 𝓡 n := by
  intro t ht
  by_contra htR
  apply ht
  rw [Tm]
  have hz : ∀ s : ℝ, F (insertLp m s t) = 0 := by
    intro s
    by_contra hne
    apply htR
    have hmem : insertLp m s t ∈ 𝓡 (n + 1) := hsupp hne
    obtain ⟨hs0, hsum, htnn⟩ := insertLp_mem_R_bounds m s t hmem
    rw [EuclideanSpace.mem_scaledStdSimplex_iff]
    exact ⟨htnn, by linarith⟩
  simp [hz]

/-- `|Tm m F t| ≤ Fmax F`. -/
theorem Tm_abs_le_Fmax (m : Fin (n + 1)) (F : ES(ℝ, n + 1) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 (n + 1))
    (t : ES(ℝ, n)) :
    |Tm m F t| ≤ MaynardSmoothY.Fmax F := by
  have hFmnn : 0 ≤ MaynardSmoothY.Fmax F := MaynardSmoothY.Fmax_nonneg F hF
  by_cases htR : t ∈ 𝓡 n
  · rw [EuclideanSpace.mem_scaledStdSimplex_iff] at htR
    obtain ⟨htnn, htsum⟩ := htR
    have hsn : 0 ≤ ∑ i, t i := Finset.sum_nonneg (fun i _ ↦ htnn i)
    have hofl : ∀ s : ℝ, (insertLp m s t).ofLp = m.insertNth s t.ofLp := by
      intro s; rw [insertLp, WithLp.ofLp_toLp]
    rw [Tm_eq_Icc m F hsupp t]
    have hbound : ∀ s ∈ Set.Icc (0 : ℝ) (1 - ∑ i, t i),
        ‖F (insertLp m s t)‖ ≤ MaynardSmoothY.Fmax F := by
      intro s hs
      rw [Set.mem_Icc] at hs
      rw [Real.norm_eq_abs]
      refine MaynardSmoothY.abs_F_le_Fmax F hF (fun i ↦ ?_)
      rw [hofl s]
      refine Fin.succAboveCases m ?_ ?_ i
      · rw [Fin.insertNth_apply_same, Set.mem_Icc]
        exact ⟨hs.1, by linarith [hs.2]⟩
      · intro j
        rw [Fin.insertNth_apply_succAbove, Set.mem_Icc]
        refine ⟨htnn j, ?_⟩
        have : t.ofLp j ≤ ∑ i, t i := Finset.single_le_sum (fun i _ ↦ htnn i) (Finset.mem_univ j)
        linarith
    have hfin : volume (Set.Icc (0 : ℝ) (1 - ∑ i, t i)) < ⊤ := (isCompact_Icc).measure_lt_top
    have hkey := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hbound
    have hmr : volume.real (Set.Icc (0 : ℝ) (1 - ∑ i, t i)) ≤ 1 := by
      rw [MeasureTheory.measureReal_def, Real.volume_Icc, sub_zero,
          ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - ∑ i, t i)]
      linarith
    calc |∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i), F (insertLp m s t)|
        = ‖∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i), F (insertLp m s t)‖ := (Real.norm_eq_abs _).symm
      _ ≤ MaynardSmoothY.Fmax F * volume.real (Set.Icc (0 : ℝ) (1 - ∑ i, t i)) := hkey
      _ ≤ MaynardSmoothY.Fmax F := by
          nlinarith [hmr, hFmnn]
  · have h0 : Tm m F t = 0 := by
      by_contra hne
      exact htR (Tm_support m F hsupp hne)
    rw [h0, abs_zero]; exact hFmnn

/-- The marginal square-integral equals `J`. -/
theorem Tm_sq_integral_eq_J (m : Fin (n + 1)) (G : ES(ℝ, n + 1) → ℝ)
    (hsupp : Function.support G ⊆ 𝓡 (n + 1))
    (hmem : MemLp G 2 (volume.restrict (𝓡 (n + 1)))) :
    ∫ t in 𝓡 n, (Tm m G t) ^ 2 = PrimeGaps.J m (hmem.toLp _) := by
  rw [J_toLp_eq_iterated n m G hmem]
  refine MeasureTheory.setIntegral_congr_fun
    isClosed_scaledStdSimplex.measurableSet (fun t _ ↦ ?_)
  rw [Tm_eq_Icc m G hsupp t]; rfl

end PrimeGaps
