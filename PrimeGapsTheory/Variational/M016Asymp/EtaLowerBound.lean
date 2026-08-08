/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Quadratic lower bound

Comparison of two scaled quadratic expressions under a bound on `μ²`.

## Main results

* `mul_sq_le_sub_one_mul_sq`: The comparison of the `k`-scaled and `(k - 1)`-scaled quadratics.
-/

@[expose] public section

namespace PrimeGaps.M016Asymp.C2_EtaLowerbound

/-- Under `k(k-1)μ² ≤ (k-T)²`, the `k`-scaled quadratic in `1 - T/k - μ` is
dominated by the `(k-1)`-scaled quadratic in `(k-T)/(k-1) - μ`. -/
theorem mul_sq_le_sub_one_mul_sq (k T μ : ℝ) (hk : 2 ≤ k)
    (hsq : k * (k - 1) * μ ^ 2 ≤ (k - T) ^ 2) :
    k * (1 - T / k - μ) ^ 2 ≤ (k - 1) * ((k - T) / (k - 1) - μ) ^ 2 := by
  rw [show k * (1 - T / k - μ) ^ 2 = ((k - T) - k * μ) ^ 2 / k by grind,
      show (k - 1) * ((k - T) / (k - 1) - μ) ^ 2 = ((k - T) - (k - 1) * μ) ^ 2 / (k - 1) by grind]
  exact (div_le_div_iff₀ (by linarith) (by linarith)).mpr (by grind)

end PrimeGaps.M016Asymp.C2_EtaLowerbound

end
