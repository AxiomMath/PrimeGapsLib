/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.DiagonalApproximation


/-!
# Retained cutoff estimates

Finite-sum, support, and integral estimates for the retained outer cutoff.
-/

@[expose] public section

open scoped Topology

open Finset MeasureTheory EuclideanSpace GPYSieveS1 MaynardSmoothY PrimeGaps
open scoped PrimeGaps PrimeGaps.sieveTruncation PrimeGaps.sieveModulus

namespace Gaps246

/-- The ordinary Maynard marginal of the fixed-width retained profile is
the square of the original rescaled marginal, multiplied by the square of
the outer ramp. -/
theorem J_smoothRetainedProfile_eq {n : ℕ} (ε η : ℝ) (hε : 0 ≤ ε) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex (n + 1) ε) :
    PrimeGaps.J m (PrimeGaps.retainedProfileLp (ε := ε) (η :=
      η) m (Grescale ε F) (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) =
        ∫ t in 𝓡 n, PrimeGaps.retainedRamp ε η m
              (EuclideanSpace.insertLp m 0 t) ^ 2 * PrimeGaps.Tm m (Grescale ε F) t ^ 2 := by
  let hPmem : MemLp (PrimeGaps.retainedProfile ε η m (Grescale ε F)) 2
        (volume.restrict (𝓡 (n + 1))) :=
    (PrimeGaps.retainedProfile_contDiff m
      (Grescale_contDiff hF)).continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact
        isCompact_scaledStdSimplex
        (PrimeGaps.retainedProfile_support m (support_rescale_subset hε hFsupp)))
  have hPsupp : Function.support (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ⊆ 𝓡 (n + 1) :=
    PrimeGaps.retainedProfile_support m (support_rescale_subset hε hFsupp)
  have hJ := PrimeGaps.Tm_sq_integral_eq_J m
      (PrimeGaps.retainedProfile ε η m (Grescale ε F)) hPsupp hPmem
  rw [show PrimeGaps.retainedProfileLp (ε := ε) (η :=
    η) m (Grescale ε F) (Grescale_contDiff hF) (support_rescale_subset hε hFsupp) =
      hPmem.toLp (PrimeGaps.retainedProfile ε η m (Grescale ε F)) by rfl]
  rw [← hJ]
  refine MeasureTheory.setIntegral_congr_fun
    isClosed_scaledStdSimplex.measurableSet
    (fun t _ ↦ ?_)
  rw [Tm_smoothRetainedProfile]
  ring

/-- For a fixed enlarged profile, the ordinary marginal of the inner
fixed-width approximation converges to the sharp retained marginal in
auxiliary-radius coordinates. -/
theorem tendsto_J_smoothRetainedProfile {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (hε : 0 ≤ ε) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex (n + 1) ε) :
    Filter.Tendsto (fun q : ℕ ↦ PrimeGaps.J m
          (PrimeGaps.retainedProfileLp (ε := ε) (η := (((q + 1 : ℕ) : ℝ)⁻¹)) m (Grescale ε F)
            (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)))
      Filter.atTop
      (𝓝 (∫ t in 𝓡 n, if (∑ i ∈ Finset.univ.erase m,
                (EuclideanSpace.insertLp m 0 t) i) ≤ PrimeGaps.retainedCutoffScale ε
          then PrimeGaps.Tm m (Grescale ε F) t ^ 2
          else 0)) := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 (n + 1) := support_rescale_subset hε hFsupp
  have hT : ContDiff ℝ (⊤ : ℕ∞) (PrimeGaps.Tm m (Grescale ε F)) :=
    PrimeGaps.Tm_contDiff m (Grescale ε F) hG hGsupp
  have hboundInt : Integrable
        (fun t : EuclideanSpace ℝ (Fin n) ↦ PrimeGaps.Tm m (Grescale ε F) t ^ 2)
        (volume.restrict (𝓡 n)) :=
    hT.continuous.continuousOn.pow 2 |>.integrableOn_compact
      isCompact_scaledStdSimplex
  rw [show (fun q : ℕ ↦ PrimeGaps.J m
        (PrimeGaps.retainedProfileLp (ε := ε) (η := (((q + 1 : ℕ) : ℝ)⁻¹)) m (Grescale ε F)
          (Grescale_contDiff hF) (support_rescale_subset hε hFsupp))) =
      fun q : ℕ ↦ ∫ t in 𝓡 n, PrimeGaps.retainedRamp ε (((q + 1 : ℕ) : ℝ)⁻¹) m
            (EuclideanSpace.insertLp m 0 t) ^ 2 * PrimeGaps.Tm m (Grescale ε F) t ^ 2 by
    funext q
    exact J_smoothRetainedProfile_eq ε _ hε m F hF hFsupp]
  apply MeasureTheory.tendsto_integral_of_dominated_convergence
    (fun t : EuclideanSpace ℝ (Fin n) ↦ PrimeGaps.Tm m (Grescale ε F) t ^ 2)
  · intro q
    have hr_eq : (fun t : EuclideanSpace ℝ (Fin n) ↦ PrimeGaps.retainedRamp ε (((q +
      1 : ℕ) : ℝ)⁻¹) m (EuclideanSpace.insertLp m 0 t)) =
        fun t : EuclideanSpace ℝ (Fin n) ↦ Real.smoothTransition
            ((PrimeGaps.retainedCutoffScale ε - ∑ j, t j) /
              (((q + 1 : ℕ) : ℝ)⁻¹)) := by
      funext t
      unfold PrimeGaps.retainedRamp
      rw [PrimeGaps.sum_erase_insertLp]
    have hr : ContDiff ℝ (⊤ : ℕ∞)
        (fun t : EuclideanSpace ℝ (Fin n) ↦ PrimeGaps.retainedRamp ε (((q + 1 : ℕ) : ℝ)⁻¹) m
            (EuclideanSpace.insertLp m 0 t)) := by
      rw [hr_eq]
      unfold PrimeGaps.retainedCutoffScale
      fun_prop
    exact ((hr.pow 2).mul (hT.pow 2)).continuous.aestronglyMeasurable
  · exact hboundInt
  · intro q
    filter_upwards with t
    have hr0 : 0 ≤ PrimeGaps.retainedRamp ε (((q + 1 : ℕ) : ℝ)⁻¹) m
        (EuclideanSpace.insertLp m 0 t) :=
      PrimeGaps.retainedRamp_nonneg _ _ _ _
    have hr1 : PrimeGaps.retainedRamp ε (((q + 1 : ℕ) : ℝ)⁻¹) m
        (EuclideanSpace.insertLp m 0 t) ≤ 1 :=
      PrimeGaps.retainedRamp_le_one _ _ _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))]
    have hrsq : PrimeGaps.retainedRamp ε (((q + 1 : ℕ) : ℝ)⁻¹) m
        (EuclideanSpace.insertLp m 0 t) ^ 2 ≤ 1 := by
      nlinarith
    calc
      PrimeGaps.retainedRamp ε (((q + 1 : ℕ) : ℝ)⁻¹) m
            (EuclideanSpace.insertLp m 0 t) ^ 2 * PrimeGaps.Tm m (Grescale ε F) t ^ 2 ≤
        1 * PrimeGaps.Tm m (Grescale ε F) t ^ 2 := mul_le_mul_of_nonneg_right hrsq (sq_nonneg _)
      _ = _ := one_mul _
  · have hnull : volume {t : EuclideanSpace ℝ (Fin n) |
          ∑ j, t j = PrimeGaps.retainedCutoffScale ε} = 0 := by
      haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
      exact MeasureTheory.volume_setOf_sum_eq (PrimeGaps.retainedCutoffScale ε)
    have hae : ∀ᵐ t : EuclideanSpace ℝ (Fin n)
        ∂volume.restrict (𝓡 n),
        (∑ j, t j) ≠ PrimeGaps.retainedCutoffScale ε := by
      exact MeasureTheory.ae_restrict_of_ae (compl_mem_ae_iff.mpr hnull)
    filter_upwards [hae] with t htne
    rw [PrimeGaps.sum_erase_insertLp]
    have hr := PrimeGaps.retainedRamp_inv_succ_tendsto ε m (EuclideanSpace.insertLp m 0 t)
    have hlim := (hr.pow 2).mul_const (PrimeGaps.Tm m (Grescale ε F) t ^ 2)
    rw [PrimeGaps.sum_erase_insertLp] at hlim
    by_cases ht : (∑ j, t j) < PrimeGaps.retainedCutoffScale ε
    · have htle : (∑ j, t j) ≤ PrimeGaps.retainedCutoffScale ε := ht.le
      simpa [ht, htle] using hlim
    · have hgt : PrimeGaps.retainedCutoffScale ε < ∑ j, t j :=
      lt_of_le_of_ne (le_of_not_gt ht) (Ne.symm htne)
      have hnle : ¬(∑ j, t j) ≤ PrimeGaps.retainedCutoffScale ε := not_le.mpr hgt
      simpa [ht, hnle] using hlim

/-- For a profile supported in an enlarged simplex, the full-line `Tm`
integral may be restricted to the nonnegative half-line. -/
theorem Tm_eq_Ici_of_enlarged_support {n : ℕ} (ε : ℝ) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hFsupp : Function.support F ⊆ enlargedSimplex (n + 1) ε)
    (t : EuclideanSpace ℝ (Fin n)) :
    PrimeGaps.Tm m F t = ∫ s in Set.Ici (0 : ℝ),
          F (EuclideanSpace.insertLp m s t) := by
  rw [PrimeGaps.Tm, ← MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero]
  intro s hs
  apply Classical.byContradiction
  intro hne
  have hmem := hFsupp hne
  have hnonneg := hmem.1 m
  rw [EuclideanSpace.insertLp_apply_same] at hnonneg
  exact hs (Set.mem_Ici.mpr hnonneg)

/-- The concrete integrand in `jEps` is the enlarged-profile `Tm`
marginal. -/
theorem jEps_inner_eq_Tm {n : ℕ} (ε : ℝ) (m : Fin (n + 1)) (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hFsupp : Function.support F ⊆ enlargedSimplex (n + 1) ε)
    (t : EuclideanSpace ℝ (Fin n)) :
    (∫ s in Set.Ici (0 : ℝ),
        F (WithLp.toLp 2 (sliceInsert (n + 1) m s t))) = PrimeGaps.Tm m F t := by
  rw [Tm_eq_Ici_of_enlarged_support ε m F hFsupp t]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ici
  intro s _
  apply congrArg F
  change WithLp.toLp 2 (sliceInsert (n + 1) m s t) = WithLp.toLp 2 (m.insertNth s t.ofLp)
  exact congrArg (WithLp.toLp 2) (sliceInsert_eq_insertNth m s t)

/-- Marginal scaling under the enlarged-to-unit-simplex rescaling. -/
theorem Tm_Grescale {n : ℕ} (ε : ℝ) (hε : 0 ≤ ε) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    PrimeGaps.Tm m (Grescale ε F) t = (1 + ε)⁻¹ *
          PrimeGaps.Tm m F ((1 + ε) • t) := by
  have ha : 0 < 1 + ε := by linarith
  unfold PrimeGaps.Tm Grescale
  simp_rw [PrimeGaps.smul_insertLp]
  have hcov := MeasureTheory.Measure.integral_comp_mul_left
    (fun u : ℝ ↦ F (EuclideanSpace.insertLp m u ((1 + ε) • t)))
    (1 + ε)
  rw [abs_of_pos (inv_pos.mpr ha), smul_eq_mul] at hcov
  exact hcov

/-- Inside the unit simplex, imposing an additional coordinate-sum cutoff
is the same as restricting to the corresponding shrunken simplex. -/
theorem integral_R_if_sum_le_eq_shrunken {n : ℕ} (c : ℝ) (hc1 : c ≤ 1)
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ t in 𝓡 n, if (∑ j, t j) ≤ c then f t else 0) =
      ∫ t in shrunkenSlice (n + 1) (1 - c), f t := by
  rw [← MeasureTheory.integral_indicator
      isClosed_scaledStdSimplex.measurableSet,
    ← MeasureTheory.integral_indicator (measurableSet_shrunkenSlice (n + 1) (1 - c))]
  apply congrArg (fun g : EuclideanSpace ℝ (Fin n) → ℝ ↦ ∫ t, g t)
  funext t
  by_cases htR : t ∈ 𝓡 n
  · rw [Set.indicator_of_mem htR]
    rw [EuclideanSpace.mem_scaledStdSimplex_iff] at htR
    obtain ⟨ht0, htsum⟩ := htR
    by_cases htc : (∑ j, t j) ≤ c
    · rw [if_pos htc, Set.indicator_of_mem]
      refine ⟨ht0, ?_⟩
      have heq : (1 : ℝ) - (1 - c) = c := by ring
      rwa [heq]
    · rw [if_neg htc, Set.indicator_of_notMem]
      exact fun hs ↦ htc (by simpa [shrunkenSlice] using hs.2)
  · rw [Set.indicator_of_notMem htR]
    rw [Set.indicator_of_notMem]
    intro hs
    apply htR
    rw [EuclideanSpace.mem_scaledStdSimplex_iff]
    refine ⟨hs.1, ?_⟩
    have hsumc : (∑ j, t j) ≤ c := by simpa [shrunkenSlice] using hs.2
    exact hsumc.trans hc1

/-- The cutoff read on the outer coordinates of a slice insertion cuts the same shrunken slice. -/
theorem integral_R_erase_sum_le_eq_shrunken {n : ℕ}
    (c : ℝ) (hc1 : c ≤ 1) (m : Fin (n + 1))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) :
    (∫ t in 𝓡 n, if (∑ i ∈ Finset.univ.erase m, (EuclideanSpace.insertLp m 0 t) i) ≤ c
        then f t else 0) = ∫ t in shrunkenSlice (n + 1) (1 - c), f t := by
  rw [← integral_R_if_sum_le_eq_shrunken c hc1 f]
  apply MeasureTheory.setIntegral_congr_fun
    isClosed_scaledStdSimplex.measurableSet
  intro t _
  dsimp only
  rw [PrimeGaps.sum_erase_insertLp]

/-- At the degenerate enlargement `ε = 1` the shrunken slice `𝓡(n, 0)` collapses to the
origin, which is null in positive dimension. -/
theorem volume_shrunkenSlice_one {n : ℕ} (hn : 1 ≤ n) :
    volume (shrunkenSlice (n + 1) (1 : ℝ)) = 0 := by
  have hsub : shrunkenSlice (n + 1) (1 : ℝ) ⊆ {0} := by
    intro x hx
    obtain ⟨hnn, hsum⟩ := EuclideanSpace.mem_scaledStdSimplex_iff.mp hx
    rw [sub_self] at hsum
    have hxi : ∀ i, x i = 0 := by
      intro i
      have hle := Finset.single_le_sum (f := fun j ↦ x j) (fun j _ ↦ hnn j) (Finset.mem_univ i)
      simp only at hle
      linarith [hnn i]
    simp only [Set.mem_singleton_iff]
    ext i
    simpa using hxi i
  refine measure_mono_null hsub ?_
  haveI : Nonempty (Fin (n + 1 - 1)) := ⟨⟨0, by omega⟩⟩
  exact measure_singleton 0

/-- At `ε = 1` the sharp retained identity holds because both sides vanish: the cutoff scale
degenerates to `0`, so both integrals run over the null shrunken slice. -/
theorem sharpRetainedIntegral_eq_jEps_div_one {n : ℕ} (hn : 1 ≤ n) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ) :
    (∫ t in 𝓡 n, if (∑ i ∈ Finset.univ.erase m, (EuclideanSpace.insertLp m 0 t) i) ≤
      PrimeGaps.retainedCutoffScale (1 : ℝ)
      then PrimeGaps.Tm m (Grescale 1 F) t ^ 2
      else 0) = jEps (n + 1) 1 m F / (1 + 1) ^ (n + 2) := by
  have hzero := volume_shrunkenSlice_one hn (n := n)
  have hc : PrimeGaps.retainedCutoffScale (1 : ℝ) = 0 := by
    rw [PrimeGaps.retainedCutoffScale]; norm_num
  have hLHS : (∫ t in 𝓡 n, if (∑ i ∈ Finset.univ.erase m, (EuclideanSpace.insertLp m 0 t) i) ≤
        PrimeGaps.retainedCutoffScale (1 : ℝ)
        then PrimeGaps.Tm m (Grescale 1 F) t ^ 2
        else 0) = 0 := by
    rw [integral_R_erase_sum_le_eq_shrunken _
        (by rw [hc]; norm_num : PrimeGaps.retainedCutoffScale (1 : ℝ) ≤ 1) m _, hc, sub_zero]
    exact setIntegral_measure_zero _ hzero
  have hRHS : jEps (n + 1) (1 : ℝ) m F = 0 := by
    rw [jEps]
    exact setIntegral_measure_zero _ hzero
  rw [hLHS, hRHS, zero_div]

/-- The sharp retained marginal in auxiliary-radius coordinates is exactly
the enlarged marginal, with the expected `(1+ε)^(n+2)` Jacobian factor. -/
theorem sharpRetainedIntegral_eq_jEps_div {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hFsupp : Function.support F ⊆ enlargedSimplex (n + 1) ε) :
    (∫ t in 𝓡 n, if (∑ i ∈ Finset.univ.erase m, (EuclideanSpace.insertLp m 0 t) i) ≤
      PrimeGaps.retainedCutoffScale ε
      then PrimeGaps.Tm m (Grescale ε F) t ^ 2
      else 0) = jEps (n + 1) ε m F / (1 + ε) ^ (n + 2) := by
  rcases hε1.lt_or_eq with hεlt | rfl
  swap
  · exact sharpRetainedIntegral_eq_jEps_div_one hn m F
  let c : ℝ := PrimeGaps.retainedCutoffScale ε
  have ha : 0 < 1 + ε := by linarith
  have hb : 0 < 1 - ε := by linarith
  have hc : c = (1 - ε) / (1 + ε) := rfl
  have hc0 : 0 < c := by rw [hc]; positivity
  have hc1 : c ≤ 1 := by
    rw [hc, div_le_one ha]
    linarith
  have hleft : (∫ t in 𝓡 n, if (∑ i ∈ Finset.univ.erase m, (EuclideanSpace.insertLp m 0 t) i) ≤ c
        then PrimeGaps.Tm m (Grescale ε F) t ^ 2
        else 0)
        =
      ∫ t in shrunkenSlice (n + 1) (1 - c),
        PrimeGaps.Tm m (Grescale ε F) t ^ 2 := by
    exact integral_R_erase_sum_le_eq_shrunken c hc1 m _
  have hcovC := shrunken_marginal_cov (k := n + 1)
    (1 - c) (by simpa using hc0)
    (fun t : EuclideanSpace ℝ (Fin n) ↦ PrimeGaps.Tm m (Grescale ε F) t ^ 2)
  have hcovE := shrunken_marginal_cov (k := n + 1)
    ε hb
    (fun t : EuclideanSpace ℝ (Fin n) ↦ PrimeGaps.Tm m F t ^ 2)
  have hj : jEps (n + 1) ε m F = ∫ t in shrunkenSlice (n + 1) ε, PrimeGaps.Tm m F t ^ 2 := by
    unfold jEps
    apply MeasureTheory.setIntegral_congr_fun (measurableSet_shrunkenSlice (n + 1) ε)
    intro t _
    dsimp only
    rw [jEps_inner_eq_Tm ε m F hFsupp t]
  have hcc : (1 : ℝ) - (1 - c) = c := by ring
  have hcovC' : (∫ t in shrunkenSlice (n + 1) (1 - c),
          PrimeGaps.Tm m (Grescale ε F) t ^ 2) = c ^ n * ∫ x in 𝓡 n,
            PrimeGaps.Tm m (Grescale ε F) (c • x) ^ 2 := by
    simpa [hcc] using hcovC
  have hcovE' : (∫ t in shrunkenSlice (n + 1) ε, PrimeGaps.Tm m F t ^ 2) = (1 - ε) ^ n * ∫ x in 𝓡 n,
            PrimeGaps.Tm m F ((1 - ε) • x) ^ 2 := by
    simpa using hcovE
  rw [hleft, hcovC', hj, hcovE']
  have hscale : ∀ t : EuclideanSpace ℝ (Fin n), (1 + ε) • (c • t) = (1 - ε) • t := by
    intro t
    rw [smul_smul, hc]
    congr 1
    field_simp
  simp_rw [Tm_Grescale ε hε m F, hscale]
  set A : ℝ := ∫ x in 𝓡 n, PrimeGaps.Tm m F ((1 - ε) • x) ^ 2
  have hint : (∫ x in 𝓡 n, ((1 + ε)⁻¹ *
            PrimeGaps.Tm m F ((1 - ε) • x)) ^ 2) = (1 + ε)⁻¹ ^ 2 * A := by
    rw [show (fun x : EuclideanSpace ℝ (Fin n) ↦ ((1 + ε)⁻¹ * PrimeGaps.Tm m F ((1 - ε) • x)) ^ 2) =
        fun x ↦ (1 + ε)⁻¹ ^ 2 *
          PrimeGaps.Tm m F ((1 - ε) • x) ^ 2 by
      funext x
      ring]
    rw [MeasureTheory.integral_const_mul]
  rw [hint]
  change c ^ n * ((1 + ε)⁻¹ ^ 2 * A) = (1 - ε) ^ n * A / (1 + ε) ^ (n + 2)
  rw [hc, div_pow, pow_add]
  field_simp

/-- Fixed-width retained marginals converge to the correctly normalized
enlarged marginal. -/
theorem tendsto_fixedWidth_J_to_jEps_div {n : ℕ} (hn : 1 ≤ n) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex (n + 1) ε) :
    Filter.Tendsto (fun q : ℕ ↦ PrimeGaps.J m
          (PrimeGaps.retainedProfileLp (ε := ε) (η := (((q + 1 : ℕ) : ℝ)⁻¹)) m (Grescale ε F)
            (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)))
      Filter.atTop
      (𝓝 (jEps (n + 1) ε m F / (1 + ε) ^ (n + 2))) := by
  rw [← sharpRetainedIntegral_eq_jEps_div hn ε hε hε1 m F hFsupp]
  exact tendsto_J_smoothRetainedProfile hn ε hε m F hF hFsupp

/-- Summed fixed-width marginals converge to the enlarged marginal sum in the second-moment
normalization. -/
theorem tendsto_fixedWidth_Jsum_to_jEps_sum {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε) :
    Filter.Tendsto (fun q : ℕ ↦ ∑ m : Fin k, (1 + ε) ^ (k + 1) * PrimeGaps.J m
            (PrimeGaps.retainedProfileLp (ε := ε) (η := (((q + 1 : ℕ) : ℝ)⁻¹)) m (Grescale ε F)
              (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)))
      Filter.atTop
      (𝓝 (∑ m : Fin k, jEps k ε m F)) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
  apply tendsto_finsetSum
  intro m _
  have hm := tendsto_fixedWidth_J_to_jEps_div
    (n := n) (by omega) ε hε hε1 m F hF hFsupp
  have hmul := hm.const_mul ((1 + ε) ^ (n + 2))
  convert hmul using 1
  have hne : (1 + ε) ^ (n + 2) ≠ 0 := by positivity
  field_simp

/-- The decoupled evaluation holds for every fixed positive smoothing width. -/
theorem fixedWidth_retainedProfile_eval {k : ℕ} (hk : 2 ≤ k) (ε η : ℝ) (hε : 0 ≤ ε)
    (m : Fin k) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      |decoupledSum (R ^ (1 + ε)) (W N)
          (PrimeGaps.retainedProfile ε η m (Grescale ε F)) m - ((W N).totient : ℝ) ^ (k + 1) *
            Real.log (R ^ (1 + ε)) ^ (k + 1) /
            (W N : ℝ) ^ (k + 1) * PrimeGaps.J m
              (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
                (Grescale_contDiff hF)
                (support_rescale_subset hε hFsupp))| ≤ C * MaynardSmoothY.Fmax
              (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ^ 2 *
            ((W N).totient : ℝ) ^ (k + 1) *
            Real.log (R ^ (1 + ε)) ^ (k + 1) /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨H, hHadm, hHcard⟩ := PrimeGaps.S2mSmooth.exists_admissible_card k
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  obtain ⟨C, hC, hev⟩ := PrimeGaps.lem_S2m_eval hk
  obtain ⟨N₀, hN₀⟩ := hev H hHadm hHcard (auxTheta δ θ ε) (auxDelta δ θ ε)
    hΘ hΔ.1 hΔ.2
    (PrimeGaps.retainedProfile ε η m (Grescale ε F))
    (PrimeGaps.retainedProfile_contDiff m (Grescale_contDiff hF))
    (PrimeGaps.retainedProfile_support m (support_rescale_subset hε hFsupp))
  exact ⟨C, hC, N₀, fun N hN ↦ by
    simpa [aux_sieveTruncation_eq, PrimeGaps.retainedProfileLp] using hN₀ N hN m⟩

/-- Fixed-width expand/drop and evaluation errors are bounded by the fixed-width error base. -/
theorem fixedWidth_inverse_error_absorb {k N : ℕ} (C δ θ ε η : ℝ) (m : Fin k)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : 1 ≤ N) (hC : 0 ≤ C)
    (hε : 0 ≤ ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hlogN : 0 < Real.log N)
    (hD0 : 0 < PrimeGaps.D₀ (N : ℝ)) :
    (N : ℝ) / (((W N).totient : ℝ) * Real.log N) * (C * MaynardSmoothY.Fmax
              (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ^ 2 *
            ((W N).totient : ℝ) ^ (k + 1) *
            Real.log (R ^ (1 + ε)) ^ (k + 1) /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))) ≤
      C * (1 + ε) ^ (k + 1) * (θ / 2 - δ) * PrimeGaps.profileSecondMomentErrorScale N R (W N)
          (MaynardSmoothY.Fmax (Grescale ε F))
          (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
  let Pm := MaynardSmoothY.Fmax (PrimeGaps.retainedProfile ε η m (Grescale ε F))
  let Fm := MaynardSmoothY.Fmax (Grescale ε F)
  let L : ℝ := Real.log N
  let D0 := PrimeGaps.D₀ (N : ℝ)
  let c := θ / 2 - δ
  let q := 1 + ε
  have hc : 0 < c := by dsimp [c]; linarith [hδ.2]
  have hφW : 0 < ((W N).totient : ℝ) := PrimeGaps.totient_W_pos
  have hWr : 0 < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hlogR : Real.log R = c * L := log_sieveTruncation N hN δ θ
  have haux : Real.log (R ^ (1 + ε)) = q * Real.log R := by
    dsimp [q]
    exact Real.log_rpow (by positivity) _
  have hPm : Pm ^ 2 ≤ Fm ^ 2 + Pm ^ 2 := by nlinarith [sq_nonneg Fm]
  have hcoef : 0 ≤ C * q ^ (k + 1) * c * ((W N).totient : ℝ) ^ k * (N : ℝ) *
        Real.log R ^ k / ((W N : ℝ) ^ (k + 1) * D0) := by
    have hq : 0 < q := by dsimp [q]; linarith
    rw [hlogR]
    positivity
  rw [PrimeGaps.profileSecondMomentErrorScale]
  change _ ≤ C * q ^ (k + 1) * c *
    ((Fm ^ 2 + Pm ^ 2) * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k /
      ((W N : ℝ) ^ (k + 1) * D0))
  rw [haux, hlogR]
  have hLne : L ≠ 0 := by simpa [L] using hlogN.ne'
  have hφWne : ((W N).totient : ℝ) ≠ 0 := hφW.ne'
  have hWrne : (W N : ℝ) ≠ 0 := hWr.ne'
  have hDne : D0 ≠ 0 := by simpa [D0] using hD0.ne'
  have hq0 : 0 ≤ q := by dsimp [q]; linarith
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  have hL0 : 0 ≤ L := hlogN.le
  have hbase : (N : ℝ) / (((W N).totient : ℝ) * L) *
        (C * Pm ^ 2 * ((W N).totient : ℝ) ^ (k + 1) * (q * (c * L)) ^ (k + 1) /
          ((W N : ℝ) ^ (k + 1) * D0)) = C * q ^ (k + 1) * c *
            (Pm ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * (c * L) ^ k /
              ((W N : ℝ) ^ (k + 1) * D0)) := by
    field_simp
    ring_nf
  rw [hbase]
  gcongr

end Gaps246
