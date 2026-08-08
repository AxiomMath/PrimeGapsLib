/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Analysis.Normed.Ring.Basic

/-!
# Properties of a reciprocal affine weight

Positivity, boundedness, continuity, and strict antitonicity of
`g A u = 1 / (1 + A * u)` on a nonnegative interval.

## Main definitions

* `g`: The reciprocal affine weight `1 / (1 + A * u)`.

## Main results

* `g_pos`: `g A` is positive on `[0, T]`.
* `g_le_one`: `g A` is at most one on `[0, T]`.
* `g_continuousOn`: `g A` is continuous on `[0, T]`.
* `g_strictAntiOn`: `g A` is strictly decreasing on `[0, T]`.
-/

@[expose] public section

namespace PrimeGaps.M016Asymp.A0_GPositive

/-- The weight function `g A u = 1 / (1 + A * u)`. -/
@[nolint defsWithUnderscore]
noncomputable def g (A : ℝ) (u : ℝ) : ℝ := 1 / (1 + A * u)

/-- `g A` is positive on `[0, T]` when `A > 0`. -/
theorem g_pos (A T : ℝ) (hA : 0 < A) : ∀ u ∈ Set.Icc (0 : ℝ) T, 0 < g A u :=
  fun _ hu ↦ div_pos zero_lt_one (by nlinarith [hu.1])

/-- `g A` is bounded above by `1` on `[0, T]` when `A > 0`. -/
theorem g_le_one (A T : ℝ) (hA : 0 < A) : ∀ u ∈ Set.Icc (0 : ℝ) T, g A u ≤ 1 :=
  fun _ hu ↦ (div_le_one (by nlinarith [hu.1])).mpr (by nlinarith [hu.1])

/-- `g A` is continuous on `[0, T]` when `A > 0`. -/
theorem g_continuousOn (A T : ℝ) (hA : 0 < A) : ContinuousOn (g A) (Set.Icc 0 T) := by
  refine ContinuousOn.div continuousOn_const
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id))
    (fun x hx ↦ ?_)
  nlinarith [hx.1]

/-- `g A` is strictly decreasing on `[0, T]` when `A > 0`. -/
theorem g_strictAntiOn (A T : ℝ) (hA : 0 < A) : StrictAntiOn (g A) (Set.Icc 0 T) :=
  fun _ hx _ _ hxy ↦
    one_div_lt_one_div_of_lt (by nlinarith [hx.1]) (by nlinarith [hx.1])

end PrimeGaps.M016Asymp.A0_GPositive

end
