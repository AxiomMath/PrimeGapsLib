/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.Certificate.ExplicitToAbstract


/-!
# A Certificate for `M_{50, 1/25} > 4`

This file states the hypothesis that an explicit certificate for `M_{50,ε} > 4` exists, and
gives the analytic realization of the `246` certificate.
-/

@[expose] public section

open MeasureTheory
open scoped PrimeGaps BigOperators

namespace PrimeGaps

/-- The analytic `L²` certificate represented by an explicit certificate. -/
noncomputable def gaps246Certificate {ε : ℚ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ct : EpsCertificateExplicit 50 ε) : EpsCertificate 50 (ε : ℝ) :=
  ct.toAbstract hε0 hε1

/-- The certified Rayleigh quotient. -/
noncomputable def gaps246CertificateRayleigh {ε : ℚ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ct : EpsCertificateExplicit 50 ε) : ℝ :=
  (∑ m, JEps (ε : ℝ) m (gaps246Certificate hε0 hε1 ct).F) / ‖(gaps246Certificate hε0 hε1 ct).F‖ ^ 2

theorem gaps246CertificateRayleigh_gt_four {ε : ℚ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (ct : EpsCertificateExplicit 50 ε) :
    4 < gaps246CertificateRayleigh hε0 hε1 ct := by
  rw [gaps246CertificateRayleigh]
  have hnorm : 0 < ‖(gaps246Certificate hε0 hε1 ct).F‖ ^ 2 := by
    refine (sq_nonneg ‖(gaps246Certificate hε0 hε1 ct).F‖).lt_of_ne fun hz ↦ ?_
    have hnorm_zero : ‖(gaps246Certificate hε0 hε1 ct).F‖ = 0 := by
      nlinarith [norm_nonneg (gaps246Certificate hε0 hε1 ct).F]
    have hF : (gaps246Certificate hε0 hε1 ct).F = 0 := norm_eq_zero.mp hnorm_zero
    simpa [hF] using (gaps246Certificate hε0 hε1 ct).cert
  exact (lt_div_iff₀ hnorm).mpr (gaps246Certificate hε0 hε1 ct).cert

end PrimeGaps
