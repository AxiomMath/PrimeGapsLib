/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.IntegralOperators


/-! # Epsilon-enlarged certificates

A certificate for `4 < M_{k, ε}` in the form of an `L²` function on the enlarged simplex
`𝓡(k, 1 + ε)` whose Rayleigh quotient exceeds `4`.

## Main definitions

* `PrimeGaps.EpsCertificate`: a non-explicit witness for `4 < M_{k, ε}`.

## Main results

* `PrimeGaps.EpsCertificate.four_lt_MEps`: a certificate gives `4 < M_{k, ε}`.
-/

@[expose] public section

open MeasureTheory

namespace PrimeGaps

/-- A non-explicit certificate for `4 < M_{k, ε}`. -/
structure EpsCertificate (k : ℕ) (ε : ℝ) where
  /-- The `L^2` function. -/
  F : Lp ℝ 2 (volume.restrict 𝓡(k, 1 + ε))
  /-- The certificate: `4 * ‖F‖ ^ 2 < ∑ m, JEps ε m F`. -/
  cert : 4 * ‖F‖ ^ 2 < ∑ m, JEps ε m F

theorem EpsCertificate.four_lt_MEps {k : ℕ} {ε : ℝ} (ct : EpsCertificate k ε) : 4 < MEps k ε := by
  grw [← MEps_ge (f := ct.F)]
  have hf : ‖ct.F‖ ≠ 0 := fun hf ↦ by
    simpa [norm_eq_zero.mp hf] using ct.cert
  exact (lt_div_iff₀ (by positivity)).mpr ct.cert

end PrimeGaps
