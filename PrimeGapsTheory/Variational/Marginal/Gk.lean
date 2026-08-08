/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import PrimeGapsTheory.Variational.M016Asymp.GPositive

/-!
# The profile `g(A, u) = 1 / (1 + A u)`

Establishes analytic properties of the reciprocal affine profile `g`.

## Main results

*  `hasDerivAt_log_div`: Gives an antiderivative of `g A`.
*  `hasDerivAt_neg_inv`: Gives an antiderivative of `(g A)²`.
*  `intervalIntegrable_g`: The profile `g A` is interval-integrable on positive intervals.
*  `intervalIntegrable_g_sq`: The square of `g A` is interval-integrable on positive intervals.
-/

@[expose] public section

open scoped Interval

namespace PrimeGaps.Gk

open PrimeGaps.M016Asymp.A0_GPositive

/-- For `A > 0` and `u ≥ 0`, the denominator `1 + A·u` is positive. -/
lemma denom_pos {A u : ℝ} (hA : 0 < A) (hu : 0 ≤ u) : 0 < 1 + A * u := by
  positivity

/-- Derivative of `log(1 + A·u) / A` is `1 / (1 + A·u)`. -/
lemma hasDerivAt_log_div (A u : ℝ) (hA : A ≠ 0) (h : 0 < 1 + A * u) :
    HasDerivAt (fun v ↦ Real.log (1 + A * v) / A) (1 / (1 + A * u)) u := by
  have h1 : HasDerivAt (fun v : ℝ ↦ (1 : ℝ) + A * v) A u := by
    simpa using ((hasDerivAt_id u).const_mul A).const_add 1
  refine ((h1.log h.ne').div_const A).congr_deriv ?_
  field_simp [hA, h.ne']

/-- Derivative of `-1/(A·(1+A·u))` is `1/(1+A·u)²`. -/
lemma hasDerivAt_neg_inv (A u : ℝ) (hA : A ≠ 0) (h : 0 < 1 + A * u) :
    HasDerivAt (fun v ↦ -(1 / (A * (1 + A * v)))) (1 / (1 + A * u) ^ 2) u := by
  have hne : A * (1 + A * u) ≠ 0 := mul_ne_zero hA h.ne'
  have h1 : HasDerivAt (fun v : ℝ ↦ A * (1 + A * v)) (A * A) u := by
    simpa using (((hasDerivAt_id u).const_mul A).const_add 1).const_mul A
  refine (((hasDerivAt_const u (1 : ℝ)).div h1 hne).neg).congr_deriv ?_
  field_simp
  ring

/-- For `A, T > 0`, `g A` is continuous on `[0, T]`. -/
lemma continuousOn_g (A T : ℝ) (hA : 0 < A) (hT : 0 < T) : ContinuousOn (g A) ([[0, T]]) := by
  refine ContinuousOn.div continuousOn_const
    (continuousOn_const.add (continuousOn_const.mul continuousOn_id)) fun u hu ↦ ?_
  rw [Set.uIcc_of_le hT.le] at hu
  exact (denom_pos hA hu.1).ne'

/-- For `A, T > 0`, `g A` is interval-integrable on `[0, T]`. -/
lemma intervalIntegrable_g (A T : ℝ) (hA : 0 < A) (hT : 0 < T) :
    IntervalIntegrable (g A) MeasureTheory.volume 0 T :=
  (continuousOn_g A T hA hT).intervalIntegrable

/-- For `A, T > 0`, `u ↦ (g A u)²` is interval-integrable on `[0, T]`. -/
lemma intervalIntegrable_g_sq (A T : ℝ) (hA : 0 < A) (hT : 0 < T) :
    IntervalIntegrable (fun u ↦ (g A u) ^ 2) MeasureTheory.volume 0 T :=
  ((continuousOn_g A T hA hT).pow 2).intervalIntegrable

end PrimeGaps.Gk

end
