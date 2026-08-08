/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import PrimeGapsTheory.Variational.Marginal.Gk

/-!
# Closed forms for weighted moments

Closed forms for the zeroth and first moments of the weight `g A u = 1 / (1 + A * u)` on
`(0, T)`.

## Main definitions

* `gamma`: The integral of `(g A u)²` on `(0, T)`.
* `mu`: The normalized first moment of `(g A u)²` on `(0, T)`.

## Main results

* `gamma_formula`: The closed form for `gamma`.
* `mu_formula`: The closed form for `mu`.
* `mu_special`: The value of `mu` when `1 + A * T = exp A`.
-/

@[expose] public section

open Real

open scoped Interval

namespace PrimeGaps.M016Asymp.A1_MuClosedForm


open MeasureTheory
open PrimeGaps.M016Asymp.A0_GPositive
open PrimeGaps.Gk

/-- The quantity $\gamma = \int_0^T g(u)^2\, du$. -/
@[nolint defsWithUnderscore]
noncomputable def gamma (A T : ℝ) : ℝ := ∫ u in (0)..T, (g A u) ^ 2

/-- The quantity $\mu = \gamma^{-1} \int_0^T u\, g(u)^2\, du$. -/
@[nolint defsWithUnderscore]
noncomputable def mu (A T : ℝ) : ℝ := (gamma A T)⁻¹ * ∫ u in (0)..T, u * (g A u) ^ 2

/-- $\int_0^T 1/(1+Au)\, du = \log(1+AT)/A$. -/
lemma integral_g_aux (A T : ℝ) (hA : 0 < A) (hT : 0 < T) :
    ∫ u in (0)..T, g A u = Real.log (1 + A * T) / A := by
  have hderiv : ∀ u ∈ ([[(0 : ℝ), T]]),
      HasDerivAt (fun v ↦ Real.log (1 + A * v) / A) (g A u) u := fun u hu ↦ by
    rw [Set.uIcc_of_le hT.le] at hu
    exact hasDerivAt_log_div A u hA.ne' (denom_pos hA hu.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_g A T hA hT)]
  simp

/-- Antiderivative identity: for $A > 0$ and $T > 0$,
    $\int_0^T (1/(1+Au))^2\, du = (1/A)(1 - 1/(1+AT))$. -/
lemma integral_g_sq_aux (A T : ℝ) (hA : 0 < A) (hT : 0 < T) :
    ∫ u in (0)..T, (g A u) ^ 2 = (1 / A) * (1 - 1 / (1 + A * T)) := by
  have hderiv : ∀ u ∈ ([[(0 : ℝ), T]]),
      HasDerivAt (fun v ↦ -(1 / (A * (1 + A * v)))) ((g A u) ^ 2) u := fun u hu ↦ by
    rw [Set.uIcc_of_le hT.le] at hu
    rw [show (g A u) ^ 2 = 1 / (1 + A * u) ^ 2 by simp [g] ]
    exact hasDerivAt_neg_inv A u hA.ne' (denom_pos hA hu.1)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (intervalIntegrable_g_sq A T hA hT)]
  field_simp
  ring

/-- Antiderivative identity: for $A > 0$ and $T > 0$,
    $\int_0^T u/(1+Au)^2\, du = (1/A^2)(\log(1+AT) - 1 + 1/(1+AT))$. -/
lemma integral_u_g_sq_aux (A T : ℝ) (hA : 0 < A) (hT : 0 < T) : ∫ u in (0)..T, u * (g A u) ^ 2 =
      (1 / A ^ 2) * (Real.log (1 + A * T) - 1 + 1 / (1 + A * T)) := by
  have heq : ∀ u ∈ ([[(0 : ℝ), T]]),
      u * (g A u) ^ 2 = (1 / A) * (g A u) - (1 / A) * (g A u) ^ 2 := fun u hu ↦ by
    rw [Set.uIcc_of_le hT.le] at hu
    have : 1 + A * u ≠ 0 := (denom_pos hA hu.1).ne'
    simp only [g]
    field_simp
    ring
  rw [intervalIntegral.integral_congr heq, intervalIntegral.integral_sub
        ((intervalIntegrable_g A T hA hT).const_mul (1 / A))
        ((intervalIntegrable_g_sq A T hA hT).const_mul (1 / A)),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_g_aux A T hA hT, integral_g_sq_aux A T hA hT]
  field_simp
  ring

/-- $1 < 1 + AT$ for $A, T > 0$. -/
lemma one_lt_one_add_AT (A T : ℝ) (hA : 0 < A) (hT : 0 < T) : 1 < 1 + A * T := by
  nlinarith [mul_pos hA hT]

/-- $0 < 1 - 1/(1 + AT)$ for $A, T > 0$. -/
lemma one_sub_inv_pos (A T : ℝ) (hA : 0 < A) (hT : 0 < T) : 0 < 1 - 1 / (1 + A * T) := by
  have h1 : 1 < 1 + A * T := one_lt_one_add_AT A T hA hT
  rw [sub_pos, div_lt_one (by linarith)]; exact h1

/-- Closed-form formula for $\gamma$. -/
theorem gamma_formula (A T : ℝ) (hA : 0 < A) (hT : 0 < T) :
    gamma A T = (1 / A) * (1 - 1 / (1 + A * T)) := by
  unfold gamma
  exact integral_g_sq_aux A T hA hT

/-- $\gamma$ is positive. -/
theorem gamma_pos (A T : ℝ) (hA : 0 < A) (hT : 0 < T) : 0 < gamma A T := by
  rw [gamma_formula A T hA hT]
  exact mul_pos (by positivity) (one_sub_inv_pos A T hA hT)

/-- Closed-form formula for $\mu$. -/
theorem mu_formula (A T : ℝ) (hA : 0 < A) (hT : 0 < T) : mu A T = (1 / A) *
      ((Real.log (1 + A * T) - 1 + (1 + A * T)⁻¹) / (1 - (1 + A * T)⁻¹)) := by
  unfold mu
  rw [gamma_formula A T hA hT, integral_u_g_sq_aux A T hA hT]
  have hAne : A ≠ 0 := hA.ne'
  have h1 : 1 < 1 + A * T := one_lt_one_add_AT A T hA hT
  have h2 : (1 : ℝ) + A * T ≠ 0 := by linarith
  have h4 : (1 : ℝ) - (1 + A * T)⁻¹ ≠ 0 := by
    rw [← one_div]; exact (one_sub_inv_pos A T hA hT).ne'
  field_simp

/-- Special case when $1 + AT = e^A$. -/
theorem mu_special (A T : ℝ) (hA : 0 < A) (hT : 0 < T) (h : 1 + A * T = rexp A) :
    mu A T = 1 / (1 - rexp (-A)) - 1 / A := by
  rw [mu_formula A T hA hT, h, Real.log_exp,
      show (rexp A)⁻¹ = rexp (-A) from (Real.exp_neg A).symm]
  have hAne : A ≠ 0 := hA.ne'
  have hexp_lt_one : rexp (-A) < 1 := by
    rw [show (1 : ℝ) = rexp 0 from (Real.exp_zero).symm]
    exact Real.exp_lt_exp.mpr (by linarith)
  have h1 : (1 : ℝ) - rexp (-A) ≠ 0 := by linarith
  field_simp
  ring

end PrimeGaps.M016Asymp.A1_MuClosedForm

end
