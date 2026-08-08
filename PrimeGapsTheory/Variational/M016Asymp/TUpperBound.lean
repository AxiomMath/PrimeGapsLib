/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Data.Int.Star

/-!
# Exponential upper bounds

Bounds for expressions formed from `T A = (exp A - 1) / A` and
`mu A = 1 / (1 - exp (-A)) - 1 / A`.

## Main definitions

* `T`: The quotient `(exp A - 1) / A`.
* `mu`: The expression `1 / (1 - exp (-A)) - 1 / A`.

## Main results

* `T_le_exp_div`: The bound `T A ≤ exp A / A` for positive `A`.
* `main_inequality`: An upper bound for `1 - T A / k - mu A`.
-/

@[expose] public section

namespace PrimeGaps.M016Asymp.A2_TUpperBound

open Real

/-- `T A = (eᴬ - 1) / A`. -/
@[nolint defsWithUnderscore]
noncomputable def T (A : ℝ) : ℝ := (rexp A - 1) / A

/-- `mu A = 1 / (1 - e⁻ᴬ) - 1 / A`. -/
@[nolint defsWithUnderscore]
noncomputable def mu (A : ℝ) : ℝ := 1 / (1 - rexp (-A)) - 1 / A

/-- For `A > 0`, `T A ≤ eᴬ / A`. -/
theorem T_le_exp_div (A : ℝ) (hA : 0 < A) : T A ≤ rexp A / A :=
  div_le_div_of_nonneg_right (by linarith) hA.le

/-- For `A > 0` and `k ≥ 2`,
`(1/A)·(1 - A/(eᴬ-1) - eᴬ/k) ≤ 1 - T A / k - mu A` (the gap is exactly `1/(A·k)`). -/
theorem main_inequality (A : ℝ) (hA : 0 < A) (k : ℤ) (hk : 2 ≤ k) :
    1 / A * (1 - A / (rexp A - 1) - rexp A / (k : ℝ)) ≤
      1 - T A / (k : ℝ) - mu A := by
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : (0 : ℤ) < k)
  have hexp_sub : 0 < rexp A - 1 := by linarith [Real.one_lt_exp_iff.mpr hA]
  have hone_sub : 0 < 1 - rexp (-A) :=
    sub_pos.mpr <| Real.exp_lt_one_iff.mpr (by linarith)
  have hexp_mul : rexp A * rexp (-A) = 1 := by rw [← Real.exp_add]; simp
  have hmu : mu A = rexp A / (rexp A - 1) - 1 / A := by
    unfold mu; field_simp; nlinarith [Real.exp_pos A, hexp_mul]
  have hgap : (1 - T A / (k : ℝ) - mu A) -
      (1 / A) * (1 - A / (rexp A - 1) - rexp A / (k : ℝ)) = 1 / (A * (k : ℝ)) := by
    rw [hmu]; unfold T; field_simp; ring
  linarith [hgap, show (0 : ℝ) < 1 / (A * (k : ℝ)) by positivity]

end PrimeGaps.M016Asymp.A2_TUpperBound

end
