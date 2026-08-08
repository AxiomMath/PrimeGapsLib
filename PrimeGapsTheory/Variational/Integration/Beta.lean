/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ForMathlib.Analysis.SpecialFunctions.Gamma.Beta

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Beta integrals

Factorial formulas and a recurrence for interval integrals of products of powers.

## Main results

* `beta_step`: The integration-by-parts recurrence for the beta integral on `(0, L)`.
* `integral_complement_pow_mul_pow_all`: The factorial formula for every real endpoint `L`.
* `integral_complement_pow_mul_pow`: The factorial formula for a nonnegative endpoint.
* `lem_beta_eval`: The beta integral on `(0, 1)` as a quotient of factorials.
-/

@[expose] public section

open scoped Nat


namespace PrimeGaps
open MeasureTheory

/-- For every real `L`, the beta integral satisfies the recurrence
`∫₀ᴸ (L-t)^(b+1) · t^k = ((b+1)/(k+1)) · ∫₀ᴸ (L-t)^b · t^(k+1)`. -/
lemma beta_step (b k : ℕ) (L : ℝ) : ∫ t in (0 : ℝ)..L, (L - t) ^ (b + 1) * t ^ k =
      ((b + 1 : ℝ) / (k + 1)) * ∫ t in (0 : ℝ)..L, (L - t) ^ b * t ^ (k + 1) := by
  have key := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := fun t ↦ (L - t) ^ (b + 1)) (v := fun t ↦ t ^ (k + 1) / (k + 1))
    (u' := fun t ↦ -((b + 1 : ℝ)) * (L - t) ^ b) (v' := fun t ↦ t ^ k)
    (a := 0) (b := L)
    (by intro x _
        have h1 : HasDerivAt (fun t : ℝ ↦ L - t) (-1) x := (hasDerivAt_id x).const_sub L
        have h2 := h1.pow (b + 1)
        simp only [Nat.add_sub_cancel] at h2
        refine h2.congr_deriv ?_
        push_cast; ring)
    (by intro x _
        have h1raw := hasDerivAt_pow (k + 1) x
        simp only [Nat.add_sub_cancel] at h1raw
        have h2 := (h1raw.congr_deriv (by push_cast; ring :
          (↑(k + 1) * x ^ (k + 1 - 1) : ℝ) = (k + 1 : ℝ) * x ^ k)).div_const (k + 1 : ℝ)
        convert h2 using 1
        field_simp)
    (by apply Continuous.intervalIntegrable; fun_prop)
    (by apply Continuous.intervalIntegrable; fun_prop)
  rw [key]
  have hint : (∫ x in (0 : ℝ)..L, -((b + 1 : ℝ)) * (L - x) ^ b * (x ^ (k + 1) / (k + 1))) =
      -((b + 1 : ℝ) / (k + 1)) * ∫ t in (0 : ℝ)..L, (L - t) ^ b * t ^ (k + 1) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ ↦ by field_simp
  rw [hint, sub_self, zero_pow (by simp), zero_pow (by simp)]
  ring

/-- For every real `L`,
`∫₀ᴸ (L - t)^b · t^k = L^(b+k+1) · (b!·k!)/((b+k+1)!)`. -/
lemma integral_complement_pow_mul_pow_all (b k : ℕ) (L : ℝ) : ∫ t in (0 : ℝ)..L, (L - t) ^ b * t ^
  k =
      L ^ (b + k + 1) * ((b ! * k ! : ℝ) / ((b + k + 1)! : ℝ)) := by
  induction b generalizing k with
  | zero =>
    simp only [pow_zero, one_mul, zero_add, Nat.factorial_zero, Nat.cast_one]
    rw [integral_pow, Nat.factorial_succ, zero_pow (by simp)]
    push_cast
    have : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp
    ring
  | succ b ih =>
    rw [beta_step, ih (k + 1), show b + (k + 1) + 1 = b + 1 + k + 1 from by ring,
      Nat.factorial_succ k, Nat.factorial_succ b]
    push_cast
    have h1 : (k : ℝ) + 1 ≠ 0 := by positivity
    have h2 : ((b + 1 + k + 1)! : ℝ) ≠ 0 := by
      exact_mod_cast (b + 1 + k + 1).factorial_ne_zero
    field_simp

/-- For `0 ≤ L`,
`∫₀ᴸ (L - t)^b · t^k = L^(b+k+1) · (b!·k!)/((b+k+1)!)`. -/
lemma integral_complement_pow_mul_pow (b k : ℕ) (L : ℝ) :
    ∫ t in (0 : ℝ)..L, (L - t) ^ b * t ^ k ∂volume = L ^ (b + k + 1) *
          ((b ! * k ! : ℝ) / ((b + k + 1)! : ℝ)) :=
  integral_complement_pow_mul_pow_all b k L

end PrimeGaps
end

@[expose] public section

open scoped Nat

namespace Real

/-- For `a, b ≥ 1`,
`∫₀¹ tᵃ⁻¹(1-t)ᵇ⁻¹ dt = (a-1)! · (b-1)! / (a+b-1)!`. -/
@[pg_tag "bg246" "lem_beta_eval"]
theorem lem_beta_eval (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) :
    (∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (b - 1)) =
      ((a - 1)! * (b - 1)! : ℝ) / ((a + b - 1)! : ℝ) := by
  rw [Nat.betaIntegral_eq_factorial_mul_div (a - 1) (b - 1),
    show (a - 1) + (b - 1) + 1 = a + b - 1 from by omega]

end Real
