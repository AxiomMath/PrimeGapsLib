/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.Certificate.Witness

/-!
# Smooth approximation of the numerical witness

The certified enlarged-simplex witness is approximated by a smooth compactly supported
function while preserving a strict Rayleigh-quotient margin.

## Main results

* `lem_mollify`: Produces a smooth enlarged witness with a strict sieve margin.
-/

@[expose] public section

open MeasureTheory EuclideanSpace
open scoped PrimeGaps Pointwise

namespace Gaps246

/-- Push a standard-simplex approximation forward to the enlarged simplex. -/
noncomputable def enlargeApprox (ε : ℝ) (G : EuclideanSpace ℝ (Fin 50) → ℝ) :
    EuclideanSpace ℝ (Fin 50) → ℝ :=
  fun y ↦ (1 + ε)⁻¹ ^ 25 * G ((1 + ε)⁻¹ • y)

theorem enlargeApprox_contDiff (ε : ℝ)
    {G : EuclideanSpace ℝ (Fin 50) → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (enlargeApprox ε G) := by
  unfold enlargeApprox
  exact contDiff_const.mul (hG.comp (contDiff_id.const_smul (1 + ε)⁻¹))

theorem enlargeApprox_support
    {ε : ℝ} (hε : 0 ≤ ε)
    {G : EuclideanSpace ℝ (Fin 50) → ℝ}
    (hG : Function.support G ⊆ 𝓡 50) :
    Function.support (enlargeApprox ε G) ⊆ enlargedSimplex 50 ε := by
  intro y hy
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  have hscale : (1 + ε)⁻¹ ^ 25 ≠ 0 := by positivity
  have hGy : G ((1 + ε)⁻¹ • y) ≠ 0 := fun hz ↦ hy (by simp [enlargeApprox, hz])
  have hx : (1 + ε)⁻¹ • y ∈ 𝓡 50 := hG hGy
  rw [← Gaps246.enlargedSimplex_eq_smul 50 hε]
  refine ⟨(1 + ε)⁻¹ • y, hx, ?_⟩
  change (1 + ε) • ((1 + ε)⁻¹ • y) = y
  rw [smul_smul, mul_inv_cancel₀ h1ε.ne', one_smul]

theorem enlargeApprox_smul (ε : ℝ) (h1ε : 1 + ε ≠ 0) (G : EuclideanSpace ℝ (Fin 50) → ℝ)
    (x : EuclideanSpace ℝ (Fin 50)) :
    enlargeApprox ε G ((1 + ε) • x) = (1 + ε)⁻¹ ^ 25 * G x := by
  unfold enlargeApprox
  congr 2
  rw [smul_smul, inv_mul_cancel₀ h1ε, one_smul]

/-- Pull the explicit enlarged-simplex polynomial back to the standard simplex with the
`L²`-normalizing factor. -/
noncomputable def standardCertificate {ε : ℚ} (ct : PrimeGaps.EpsCertificateExplicit 50 ε)
    (x : EuclideanSpace ℝ (Fin 50)) : ℝ :=
  (1 + (ε : ℝ)) ^ 25 * ct.polynomial ((1 + (ε : ℝ)) • x)

theorem standardCertificate_continuous {ε : ℚ}
    (ct : PrimeGaps.EpsCertificateExplicit 50 ε) : Continuous (standardCertificate ct) := by
  exact continuous_const.mul
    (ct.continuous_polynomial.comp (continuous_id.const_smul (1 + (ε : ℝ))))

theorem standardCertificate_memLp {ε : ℚ} (ct : PrimeGaps.EpsCertificateExplicit 50 ε) :
    MemLp (standardCertificate ct) 2 (volume.restrict (𝓡 50)) := by
  haveI : IsFiniteMeasure (volume.restrict (𝓡 50)) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (isCompact_scaledStdSimplex (k := 50) (s := 1)).measure_lt_top⟩
  obtain ⟨C, hC⟩ :=
    (isCompact_scaledStdSimplex (k := 50) (s := 1)).exists_bound_of_continuousOn
      (standardCertificate_continuous ct).continuousOn
  refine MemLp.of_bound (standardCertificate_continuous ct).aestronglyMeasurable C ?_
  rw [ae_restrict_iff' (isClosed_scaledStdSimplex (k := 50) (s := 1)).measurableSet]
  exact Filter.Eventually.of_forall hC

/-- Squared `L²` error is preserved by the certificate's dimension-50,
Jacobian-normalised scaling. -/
theorem enlargeApprox_error_integral
    {ε : ℚ} (hε : 0 ≤ ε) (ct : PrimeGaps.EpsCertificateExplicit 50 ε)
    (G : EuclideanSpace ℝ (Fin 50) → ℝ) :
    (∫ y in enlargedSimplex 50 (ε : ℝ), (ct.polynomial y - enlargeApprox (ε : ℝ) G y) ^ 2) =
      ∫ x in 𝓡 50, (standardCertificate ct x - G x) ^ 2 := by
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε
  have h1ε : (0 : ℝ) < 1 + (ε : ℝ) := by linarith
  let H : EuclideanSpace ℝ (Fin 50) → ℝ := fun y ↦ (ct.polynomial y - enlargeApprox (ε : ℝ) G y) ^ 2
  have hset : (1 + (ε : ℝ)) • 𝓡 50 = enlargedSimplex 50 (ε : ℝ) :=
    Gaps246.enlargedSimplex_eq_smul 50 hεR
  have hcov := MeasureTheory.Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (EuclideanSpace ℝ (Fin 50))) H (𝓡 50) h1ε
  rw [finrank_euclideanSpace_fin, hset] at hcov
  have hpoint : ∀ x : EuclideanSpace ℝ (Fin 50), H ((1 + (ε : ℝ)) • x) =
        (1 + (ε : ℝ))⁻¹ ^ 50 * (standardCertificate ct x - G x) ^ 2 := by
    intro x
    rw [show H ((1 + (ε : ℝ)) • x) = (ct.polynomial ((1 + (ε : ℝ)) • x) -
          enlargeApprox (ε : ℝ) G ((1 + (ε : ℝ)) • x)) ^ 2 by rfl,
      enlargeApprox_smul (ε : ℝ) h1ε.ne']
    unfold standardCertificate
    field_simp [h1ε.ne']
  have hlhs : (∫ x in 𝓡 50, H ((1 + (ε : ℝ)) • x)) = (1 + (ε : ℝ))⁻¹ ^ 50 *
        ∫ x in 𝓡 50, (standardCertificate ct x - G x) ^ 2 := by
    simp_rw [hpoint]
    rw [MeasureTheory.integral_const_mul]
  rw [hlhs] at hcov
  change (∫ y in enlargedSimplex 50 (ε : ℝ), (ct.polynomial y - enlargeApprox (ε : ℝ) G y) ^ 2) =
    ∫ x in 𝓡 50, (standardCertificate ct x - G x) ^ 2
  have hc : (1 + (ε : ℝ))⁻¹ ^ 50 ≠ 0 := by positivity
  have hinv : ((1 + (ε : ℝ)) ^ 50)⁻¹ = (1 + (ε : ℝ))⁻¹ ^ 50 := (inv_pow (1 + (ε : ℝ)) 50).symm
  rw [hinv, smul_eq_mul] at hcov
  exact (mul_left_cancel₀ hc hcov).symm

/-- **Exact numerical room for the 246 witness.**  The certificate inequality
`2/θ < C` leaves a positive interval of levels `δ` for which the witness
inequality remains strict. -/
theorem certificate_delta_witness_room (θ C : ℝ) (hθ : 0 < θ) (hcert : 2 / θ < C) :
    ∃ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) (θ / 2) ∧
      1 < (θ / 2 - δ) * C := by
  have hQ : 0 < C := lt_trans (div_pos (by norm_num) hθ) hcert
  have hθQ : 2 < θ * C := by
    rw [div_lt_iff₀ hθ] at hcert
    simpa [mul_comm] using hcert
  set hi : ℝ := θ / 2 - 1 / C with hhi
  have hhi0 : 0 < hi := by
    rw [hhi, sub_pos, div_lt_iff₀ hQ]
    nlinarith
  have hhiθ : hi < θ / 2 := by
    rw [hhi]
    have : 0 < 1 / C := by positivity
    linarith
  refine ⟨hi / 2, ⟨by linarith, by linarith⟩, ?_⟩
  rw [hhi]
  field_simp [hQ.ne']
  nlinarith

/-- Smooth, enlarged-simplex-supported functions are dense at the certified
enlarged witness, in the exact `L²` metric used by the continuous quotient. -/
theorem exists_smooth_enlarged_close {ε : ℚ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ct : PrimeGaps.EpsCertificateExplicit 50 ε) (r : ℝ) (hr : 0 < r) :
    ∃ F : EuclideanSpace ℝ (Fin 50) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      Function.support F ⊆ enlargedSimplex 50 (ε : ℝ) ∧
      ∃ hF : MemLp F 2 (volume.restrict (enlargedSimplex 50 (ε : ℝ))),
        dist (hF.toLp F) (PrimeGaps.gaps246Certificate hε0 hε1 ct).F < r := by
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε0
  obtain ⟨G, hGdiff, hGtsupp, hGclose⟩ :=
    PrimeGaps.smooth_L2_approx_on_simplex 50 (by omega)
      (standardCertificate ct) (standardCertificate_memLp ct) r hr
  let F := enlargeApprox (ε : ℝ) G
  have hFsupp : Function.support F ⊆ enlargedSimplex 50 (ε : ℝ) :=
    enlargeApprox_support hεR (subset_trans (subset_tsupport G) hGtsupp)
  have hFdiff : ContDiff ℝ (⊤ : ℕ∞) F := enlargeApprox_contDiff (ε : ℝ) hGdiff
  have hFmem : MemLp F 2 (volume.restrict (enlargedSimplex 50 (ε : ℝ))) :=
    hFdiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact
        (isCompact_enlargedSimplex 50 (ε : ℝ)) hFsupp)
  refine ⟨F, hFdiff, hFsupp, hFmem, ?_⟩
  let hpoly : MemLp ct.polynomial 2
      (volume.restrict (enlargedSimplex 50 (ε : ℝ))) := ct.polynomial_memLp
  have hcertificateF : (PrimeGaps.gaps246Certificate hε0 hε1 ct).F = hpoly.toLp ct.polynomial :=
    rfl
  rw [hcertificateF, dist_toLp_toLp_eq_eLpNorm F ct.polynomial hFmem hpoly]
  change (eLpNorm (F - ct.polynomial) 2 (volume.restrict (enlargedSimplex 50 (ε : ℝ)))).toReal < r
  rw [eLpNorm_sub_comm]
  change (eLpNorm (fun x ↦ ct.polynomial x - F x) 2
    (volume.restrict (enlargedSimplex 50 (ε : ℝ)))).toReal < r
  have hErrMem : MemLp (fun x ↦ ct.polynomial x - F x) 2
      (volume.restrict (enlargedSimplex 50 (ε : ℝ))) := hpoly.sub hFmem
  rw [eLpNorm_two_eq_ofReal_sqrt_integral_sq
      hErrMem.aestronglyMeasurable hErrMem,
    enlargeApprox_error_integral hε0 ct G]
  have hstdmem : MemLp (fun x ↦ standardCertificate ct x - G x) 2
      (volume.restrict (𝓡 50)) := (standardCertificate_memLp ct).sub
    (hGdiff.continuous.memLp_of_hasCompactSupport (HasCompactSupport.of_support_subset_isCompact
        isCompact_scaledStdSimplex
        (subset_trans (subset_tsupport G) hGtsupp)))
  rw [← eLpNorm_two_eq_ofReal_sqrt_integral_sq
      hstdmem.aestronglyMeasurable hstdmem]
  exact hGclose

/-- **`lem_mollify`** (certificate → smooth witness). Under certificate-admissibility of the
level `θ` for the supplied enlargement `ε`, there is a smooth witness `F` supported on the
enlarged simplex `𝒯_ε` and a level margin `δ ∈ (0, θ/2)` respecting the weak enlargement
room `(1+ε)·θ < 1`, for which the (`ρ = 1`) sieve witness inequality holds:
`∫_{𝒯_ε} F² < (θ/2 − δ)·∑ₘ Jᵐ_ε(F)`.

Bridges the abstract certificate produced by `EpsCertificateExplicit.toAbstract` through the
enlarged mollification; the mollification / numeric-margin step is the isolated analytic node. -/
theorem lem_mollify {ε : ℚ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ct : PrimeGaps.EpsCertificateExplicit 50 ε) (θ : ℝ)
    (hθthr : 2 / θ < PrimeGaps.gaps246CertificateRayleigh hε0 hε1 ct)
    (hθε : 1 + (ε : ℝ) < 1 / θ) :
    ∃ F : EuclideanSpace ℝ (Fin 50) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      Function.support F ⊆ enlargedSimplex 50 (ε : ℝ) ∧
      ∃ δ : ℝ, δ ∈ Set.Ioo (0 : ℝ) (θ / 2) ∧ (1 + (ε : ℝ)) * θ < 1 ∧
        (∫ x in enlargedSimplex 50 (ε : ℝ), (F x) ^ 2) <
          (θ / 2 - δ) * (∑ m, jEps 50 (ε : ℝ) m F) := by
  have hεR : (0 : ℝ) ≤ (ε : ℝ) := by exact_mod_cast hε0
  let Q₀ := PrimeGaps.gaps246CertificateRayleigh hε0 hε1 ct
  let C := (2 / θ + Q₀) / 2
  change 2 / θ < Q₀ at hθthr
  have hCQ : C < Q₀ := by
    dsimp only [C]
    linarith
  have hθC : 2 / θ < C := by
    dsimp only [C]
    linarith
  have hθpos : 0 < θ := by
    have hinvpos : 0 < 1 / θ := lt_of_lt_of_le
      (by linarith : (0 : ℝ) < 1 + (ε : ℝ)) hθε.le
    exact (one_div_pos).mp hinvpos
  have hweak : (1 + (ε : ℝ)) * θ < 1 := by
    rw [lt_div_iff₀ hθpos] at hθε
    simpa [mul_comm] using hθε
  let f₀ : EnlargedLp 50 (ε : ℝ) := (PrimeGaps.gaps246Certificate hε0 hε1 ct).F
  have hf₀den_ne : enlargedDenominator f₀ ≠ 0 := by
    intro hz
    have hnorm_zero : ‖f₀‖ = 0 := by
      rw [enlargedDenominator] at hz
      nlinarith [norm_nonneg f₀]
    have hf₀zero : f₀ = 0 := norm_eq_zero.mp hnorm_zero
    have hcert := (PrimeGaps.gaps246Certificate hε0 hε1 ct).cert
    change 4 * ‖f₀‖ ^ 2 < ∑ m, PrimeGaps.JEps (ε : ℝ) m f₀ at hcert
    have hJEpsZero (m : Fin 50) : PrimeGaps.JEps (ε : ℝ) m
          (0 : Lp ℝ 2 (volume.restrict 𝓡(50, 1 + (ε : ℝ)))) = 0 := by
      rw [PrimeGaps.JEps_apply]
      simp
    rw [hf₀zero] at hcert
    norm_num only [norm_zero, pow_two, zero_mul] at hcert
    change 0 < ∑ m, PrimeGaps.JEps (ε : ℝ) m
      (0 : Lp ℝ 2 (volume.restrict 𝓡(50, 1 + (ε : ℝ)))) at hcert
    simp_rw [hJEpsZero] at hcert
    norm_num at hcert
  have hf₀ray : C < enlargedRayleigh (ε : ℝ) f₀ := by
    rwa [enlargedRayleigh_eq_shared]
  have hcont := continuousAt_enlargedRayleigh (ε : ℝ) f₀ hf₀den_ne
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨r, hr, hstay⟩ := hcont (enlargedRayleigh (ε : ℝ) f₀ - C) (sub_pos.mpr hf₀ray)
  obtain ⟨F, hFdiff, hFsupp, hFmem, hFclose⟩ := exists_smooth_enlarged_close hε0 hε1 ct r hr
  have hFdist : dist (enlargedRayleigh (ε : ℝ) (hFmem.toLp F)) (enlargedRayleigh (ε : ℝ) f₀) <
        enlargedRayleigh (ε : ℝ) f₀ - C :=
    hstay hFclose
  have hFray : C < enlargedRayleigh (ε : ℝ) (hFmem.toLp F) := by
    rw [Real.dist_eq, abs_lt] at hFdist
    linarith [hFdist.1]
  have hqF : C < qEps 50 (ε : ℝ) F := by
    rw [← enlargedRayleigh_toLp_eq_qEps (ε : ℝ)
      F hFmem (fun x hx ↦ by
        by_contra hFx
        exact hx (hFsupp hFx))]
    exact hFray
  obtain ⟨δ, hδ, hδroom⟩ := certificate_delta_witness_room θ C hθpos hθC
  refine ⟨F, hFdiff, hFsupp, δ, hδ, hweak, ?_⟩
  let D : ℝ := ∫ x in enlargedSimplex 50 (ε : ℝ), (F x) ^ 2
  let N : ℝ := ∑ m, jEps 50 (ε : ℝ) m F
  have hCpos : 0 < C := lt_trans (div_pos (by norm_num) hθpos) hθC
  have hDnonneg : 0 ≤ D := integral_nonneg fun x ↦ sq_nonneg (F x)
  have hDne : D ≠ 0 := by
    intro hDz
    rw [qEps,
      show (∫ x in enlargedSimplex 50 (ε : ℝ), F x ^ 2) = D by rfl,
      hDz, div_zero] at hqF
    linarith
  have hDpos : 0 < D := hDnonneg.lt_of_ne hDne.symm
  have hqmul : C * D < N := by
    rw [qEps,
      show (∫ x in enlargedSimplex 50 (ε : ℝ), F x ^ 2) = D by rfl,
      show (∑ m, jEps 50 (ε : ℝ) m F) = N by rfl,
      lt_div_iff₀ hDpos] at hqF
    exact hqF
  have ha : 0 < θ / 2 - δ := sub_pos.mpr hδ.2
  have hfirst : D < ((θ / 2 - δ) * C) * D :=
    by simpa using mul_lt_mul_of_pos_right hδroom hDpos
  have hsecond : ((θ / 2 - δ) * C) * D < (θ / 2 - δ) * N := by
    rw [mul_assoc]
    exact mul_lt_mul_of_pos_left hqmul ha
  exact hfirst.trans hsecond

end Gaps246
