/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.Core


/-!
# Retained profiles

Definitions and support properties for the retained and discarded transformed weights.
-/

@[expose] public section

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY
open scoped PrimeGaps

namespace Gaps246

open scoped Pointwise in
/-- **Shrunken-slice change of variables.** The
integral over the ε-shrunken `(k−1)`-slice `𝒮_ε = shrunkenSlice k ε` equals `(1−ε)^{k−1}`
times the integral over `𝓡 (k−1)` of the `(1−ε)`-rescaled integrand.  This is the
substitution `s = (1−ε)•u`, which maps `𝓡 (k−1)` diffeomorphically onto `𝒮_ε` and
multiplies the `(k−1)`-dimensional Lebesgue measure by `(1−ε)^{k−1}`. -/
theorem shrunken_marginal_cov {k : ℕ} (ε : ℝ) (hε1 : 0 < 1 - ε)
    (G : EuclideanSpace ℝ (Fin (k - 1)) → ℝ) :
    ∫ x in shrunkenSlice k ε, G x = (1 - ε) ^ (k - 1) * ∫ x in 𝓡 (k - 1), G ((1 - ε) • x) :=
  setIntegral_scaledStdSimplex hε1 G

theorem outerCutoff_iff_aux_logCoord_sum_le_pre {k N : ℕ}
    {δ θ ε : ℝ} {m : Fin k} {ρ : Fin k → ℕ}
    (hN : 1 ≤ N) (hε : 0 ≤ ε)
    (hR : 1 < PrimeGaps.sieveTruncation N δ θ)
    (hρpos : ∀ i ∈ Finset.univ.erase m, 0 < ρ i) :
    PrimeGaps.outerProductCutoff ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m ρ ↔
      (∑ i ∈ Finset.univ.erase m, Real.log (ρ i : ℝ) /
        Real.log ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))) ≤
          PrimeGaps.retainedCutoffScale ε := by
  unfold PrimeGaps.outerProductCutoff PrimeGaps.retainedCutoffScale
  have hq : 0 < 1 + ε := by linarith
  have hlogR : 0 < Real.log (PrimeGaps.sieveTruncation N δ θ) := Real.log_pos hR
  have hprodpos : (0 : ℝ) < ∏ i ∈ Finset.univ.erase m, (ρ i : ℝ) := by
    apply Finset.prod_pos
    intro i hi
    exact_mod_cast hρpos i hi
  have haux : Real.log ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) =
      (1 + ε) * Real.log (PrimeGaps.sieveTruncation N δ θ) :=
    Real.log_rpow (by positivity) (1 + ε)
  rw [← Real.log_le_log_iff hprodpos (by positivity)]
  rw [Real.log_prod (fun i hi ↦ by
    exact ne_of_gt (by exact_mod_cast hρpos i hi : (0 : ℝ) < ρ i))]
  rw [Real.log_rpow (by linarith), haux, ← Finset.sum_div]
  have hfrac : (∑ i ∈ Finset.univ.erase m, Real.log (ρ i : ℝ)) /
          ((1 + ε) * Real.log (PrimeGaps.sieveTruncation N δ θ)) =
        ((∑ i ∈ Finset.univ.erase m, Real.log (ρ i : ℝ)) /
            Real.log (PrimeGaps.sieveTruncation N δ θ)) / (1 + ε) := by
    field_simp
  rw [hfrac, div_le_div_iff_of_pos_right hq, div_le_iff₀ hlogR]

/-- The retained ramp reads only the outer coordinates, so rescaling the pinned coordinate `m`
by any `u` leaves it unchanged. -/
theorem retainedRamp_logCoord_update {k : ℕ} (ε η : ℝ) (m : Fin k) (ρ : Fin k → ℕ) (u : ℕ)
    (L : ℝ) :
    PrimeGaps.retainedRamp ε η m
        (WithLp.toLp 2 (fun i ↦ Real.log ((Function.update ρ m u) i : ℝ) / L)) =
      PrimeGaps.retainedRamp ε η m (WithLp.toLp 2 (fun i ↦ Real.log (ρ i : ℝ) / L)) := by
  unfold PrimeGaps.retainedRamp
  congr 2
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have him : i ≠ m := (Finset.mem_erase.mp hi).1
  change Real.log ((Function.update ρ m u) i : ℝ) / L = Real.log (ρ i : ℝ) / L
  rw [Function.update_of_ne him]

theorem Ydisc_smoothRetainedProfile {k N : ℕ} (δ θ ε η : ℝ)
    (m : Fin k) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (ρ : Fin k → ℕ) :
    PrimeGaps.Ydisc (PrimeGaps.sieveTruncation N δ θ) (PrimeGaps.sieveModulus N)
        (PrimeGaps.retainedProfile ε η m (Grescale ε F)) m ρ = PrimeGaps.retainedRamp ε η m
          (WithLp.toLp 2 (fun i ↦ Real.log (ρ i : ℝ) /
              Real.log (PrimeGaps.sieveTruncation N δ θ))) *
        PrimeGaps.Ydisc (PrimeGaps.sieveTruncation N δ θ) (PrimeGaps.sieveModulus N)
            (Grescale ε F) m ρ := by
  unfold PrimeGaps.Ydisc
  rw [← tsum_mul_left]
  apply tsum_congr
  intro u
  by_cases hu : u.Coprime (PrimeGaps.sieveModulus N) ∧ Squarefree u
  · rw [if_pos hu, if_pos hu, PrimeGaps.retainedProfile]
    rw [retainedRamp_logCoord_update ε η m ρ u
      (Real.log (PrimeGaps.sieveTruncation N δ θ))]
    ring
  · rw [if_neg hu, if_neg hu, mul_zero]

/-- Continuous analogue of `Ydisc_smoothRetainedProfile`: the ramp factors
exactly out of the ordinary marginal integral. -/
theorem Tm_smoothRetainedProfile {n : ℕ} (ε η : ℝ) (m : Fin (n + 1))
    (F : EuclideanSpace ℝ (Fin (n + 1)) → ℝ)
    (t : EuclideanSpace ℝ (Fin n)) :
    PrimeGaps.Tm m (PrimeGaps.retainedProfile ε η m (Grescale ε F)) t = PrimeGaps.retainedRamp ε η m
          (EuclideanSpace.insertLp m 0 t) * PrimeGaps.Tm m (Grescale ε F) t := by
  unfold PrimeGaps.Tm
  rw [← MeasureTheory.integral_const_mul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with s
  rw [PrimeGaps.retainedProfile, PrimeGaps.retainedRamp_insertLp ε η m s 0 t]

/-- The fixed-width ramp factors exactly through the coupled inverse
marginal as well as through `Ydisc`. -/
theorem yInverseSum_smoothRetainedAux {k N : ℕ} (hk : 2 ≤ k)
    (hN : 0 < N) (δ θ ε η : ℝ) (hε : 0 ≤ ε) (m : Fin k)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (r : Fin k → ℕ) :
    PrimeGaps.yInverseSum (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N)
        (fun x ↦ PrimeGaps.retainedProfile ε η m (Grescale ε F) (WithLp.toLp 2 x.ofLp))) m r =
      PrimeGaps.retainedRamp ε η m (WithLp.toLp 2 (fun i ↦ Real.log (r i : ℝ) /
          Real.log ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)))) *
        PrimeGaps.yInverseSum (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
          (PrimeGaps.sieveModulus N)
          (fun x ↦ Grescale ε F (WithLp.toLp 2 x.ofLp))) m r := by
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k := support_rescale_subset hε hFsupp
  have hP : ContDiff ℝ (⊤ : ℕ∞) (PrimeGaps.retainedProfile ε η m (Grescale ε F)) :=
    PrimeGaps.retainedProfile_contDiff m (Grescale_contDiff hF)
  have hPsupp : Function.support (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ⊆ 𝓡 k :=
    PrimeGaps.retainedProfile_support m (support_rescale_subset hε hFsupp)
  have hRaux : 0 < (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := Real.rpow_pos_of_pos
      (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) _
  unfold PrimeGaps.yInverseSum
  simp_rw [MaynardSmoothY.y_from_lambda_smooth ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
    (PrimeGaps.sieveModulus N) (PrimeGaps.retainedProfile ε η m (Grescale ε F)) hk hRaux
    hP.continuous hPsupp]
  simp_rw [MaynardSmoothY.y_from_lambda_smooth ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
    (PrimeGaps.sieveModulus N) (Grescale ε F) hk hRaux hG.continuous hGsupp]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro a
  by_cases ha : Squarefree (∏ i, (Function.update r m a) i) ∧
        (∏ i, (Function.update r m a) i).Coprime (PrimeGaps.sieveModulus N)
  · rw [if_pos ha, if_pos ha, PrimeGaps.retainedProfile]
    rw [retainedRamp_logCoord_update ε η m r a
      (Real.log ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)))]
    ring
  · rw [if_neg ha, if_neg ha]
    simp

/-- The enlarged weight is the ordinary `l₀` weight at the enlarged radius. -/
theorem lambdaEpsAux_coe {k N : ℕ} {δ θ ε : ℝ}
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    ⇑(PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
      (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) =
        lambdaEps k N δ θ ε F := by
  rw [← aux_sieveTruncation_eq]
  exact (lambdaEps_eq_l₀_aux F hN hε).symm

/-- The transformed maximum of the enlarged weight is at most `Fmax` of the rescaled test
function. -/
theorem maxRealAbs_l₀_le_Fmax {k N : ℕ} (hk : 2 ≤ k) (hN : 0 < N) (δ θ ε : ℝ)
    {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F))
    (hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k) :
    (PrimeGaps.lToY (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))).maxRealAbs ≤
      MaynardSmoothY.Fmax (Grescale ε F) :=
  MaynardSmoothY.maxRealAbs_lambda0_le_Fmax _ (PrimeGaps.sieveModulus N) (Grescale ε F) hk
    (Real.rpow_pos_of_pos (Real.rpow_pos_of_pos (by exact_mod_cast hN) _) _) hG hGsupp

/-- The retained weight's transformed maximum inherits that bound. -/
theorem maxRealAbs_retainedL_le_Fmax {k N : ℕ} (hk : 2 ≤ k) (hN : 0 < N) (δ θ ε : ℝ) (m : Fin k)
    {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F))
    (hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k) :
    (PrimeGaps.lToY (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
        (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) (PrimeGaps.sieveModulus N)
          (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤
      MaynardSmoothY.Fmax (Grescale ε F) :=
  (PrimeGaps.maxRealAbs_retainedL_le _ m _).trans (maxRealAbs_l₀_le_Fmax hk hN δ θ ε hG hGsupp)

/-- The discarded weight's transformed maximum inherits that bound. -/
theorem maxRealAbs_discardedL_le_Fmax {k N : ℕ} (hk : 2 ≤ k) (hN : 0 < N) (δ θ ε : ℝ) (m : Fin k)
    {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F))
    (hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k) :
    (PrimeGaps.lToY (PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
        (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) (PrimeGaps.sieveModulus N)
          (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤
      MaynardSmoothY.Fmax (Grescale ε F) :=
  (PrimeGaps.maxRealAbs_discardedL_le _ m _).trans (maxRealAbs_l₀_le_Fmax hk hN δ θ ε hG hGsupp)

/-- The enlarged second moment dominates the retained square plus twice the mixed term. -/
theorem corrected_retained_split_lower {k N : ℕ} (hN : 1 ≤ N)
    (h : Fin k → ℕ) (δ θ ε : ℝ) (hε : 0 ≤ ε) (m : Fin k)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (w₀ : ZMod (PrimeGaps.sieveModulus N)) :
    PrimeGaps.S₂m h (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
          (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
            (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) N w₀ m +
        2 * PrimeGaps.bilinearPrimeSum h N m
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
            (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
              (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
            (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
              (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) w₀ ≤
      PrimeGaps.S₂m h (lambdaEps k N δ θ ε F) N w₀ m := by
  apply PrimeGaps.bilinear_split_lower h N m (lambdaEps k N δ θ ε F)
    (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
    (⇑(PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
  intro d
  have hadd := congrArg (fun L : (Fin k → ℕ) →₀ ℝ ↦ L d)
    (PrimeGaps.retainedL_add_discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
  rw [Finsupp.add_apply] at hadd
  rw [hadd]
  exact congrFun (lambdaEpsAux_coe F hN hε) d

/-- Ordinary permissible support at the enlarged radius implies `epsPermissible` support. -/
theorem epsPermissible_of_enlarged_hasPermissibleSupport {k N : ℕ} {δ θ ε : ℝ}
    {L : (Fin k → ℕ) →₀ ℝ}
    (hL : L.HasPermissibleSupport
      ⌊(PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)⌋₊
      (PrimeGaps.sieveModulus N)) :
    epsPermissible k N δ θ ε ⇑L := by
  intro d hbad
  by_contra hd
  have hp := Finset.mem_permissibleSupport_iff'.mp (hL (Finsupp.mem_support_iff.mpr hd))
  apply hbad
  refine ⟨(fun i ↦ Nat.one_le_iff_ne_zero.mpr (hp.1 i)), ?_, hp.2.2.1, hp.2.2.2⟩
  calc (∏ i, d i : ℝ)
      ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := by
        simpa [Nat.cast_prod] using PrimeGaps.cast_prod_le_of_mem_permissibleSupport
          (hL (Finsupp.mem_support_iff.mpr hd))

theorem lambdaRetained_epsPermissible (k N : ℕ) (δ θ ε : ℝ) (m : Fin k)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) :
    epsPermissible k N δ θ ε ⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) :=
  epsPermissible_of_enlarged_hasPermissibleSupport
    (PrimeGaps.retainedL_hasPermissibleSupport _ _ _ PrimeGaps.hasPermissibleSupport_l₀)

theorem lambdaDiscarded_epsPermissible (k N : ℕ) (δ θ ε : ℝ) (m : Fin k)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) :
    epsPermissible k N δ θ ε ⇑(PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) :=
  epsPermissible_of_enlarged_hasPermissibleSupport
    (PrimeGaps.discardedL_hasPermissibleSupport _ _ _ PrimeGaps.hasPermissibleSupport_l₀)

/-- The discarded complement retains the full enlarged outer support bound.
Together with the retained `R^(1-ε)` bound this is the exponent pair
`(1-ε,1+ε)` whose sum is exactly `2`. -/
theorem lambdaDiscarded_outer_support_enlarged (k N : ℕ) (δ θ ε : ℝ)
    (m : Fin k) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (d : Fin k → ℕ)
    (hd : PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
        (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) d ≠ 0) :
    (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := by
  have hall := epsPermissible_conditions (lambdaDiscarded_epsPermissible k N δ θ ε m F) hd
  have hsub : (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ ∏ i, (d i : ℝ) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i ↦ (d i : ℝ)) (Finset.mem_univ m)]
    exact le_mul_of_one_le_left
      (Finset.prod_nonneg fun i _ ↦ Nat.cast_nonneg (d i))
      (by exact_mod_cast hall.1 m)
  exact hsub.trans hall.2.1

end Gaps246
