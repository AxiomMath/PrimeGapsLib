/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.Simplex

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Extension by zero from the simplex

Extension by zero of a function on the standard solid simplex `𝓡 k`.

## Main definitions

* `F_P`: The extension of `P` by zero outside `𝓡 k`.

## Main results

* `F_P_eq_on_R`: The function `F_P P` agrees with `P` on `𝓡 k`.
* `F_P_eq_zero_off_R`: The function `F_P P` vanishes outside `𝓡 k`.
-/

@[expose] public section

open scoped PrimeGaps

namespace PrimeGaps

/-- The extension by zero of `P` outside the simplex `𝓡 k`. -/
@[pg_tag "bg246" "def_polynomial_F", nolint defsWithUnderscore]
noncomputable def F_P {k : ℕ} (P : EuclideanSpace ℝ (Fin k) → ℝ) : EuclideanSpace ℝ (Fin k) → ℝ :=
  fun x ↦ (𝓡 k).indicator P x

/-- On the simplex, `F_P` agrees with `P`. -/
lemma F_P_eq_on_R {k : ℕ} {P : EuclideanSpace ℝ (Fin k) → ℝ}
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ 𝓡 k) : F_P P x = P x :=
  Set.indicator_of_mem hx P

/-- Off the simplex, `F_P` vanishes. -/
lemma F_P_eq_zero_off_R {k : ℕ} {P : EuclideanSpace ℝ (Fin k) → ℝ}
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∉ 𝓡 k) : F_P P x = 0 :=
  Set.indicator_of_notMem hx P

end PrimeGaps
