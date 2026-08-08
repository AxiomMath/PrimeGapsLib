/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import PrimeGapsTheory.ForMathlib.NumberTheory.Divisors

import PrimeGapsTheory.ForMathlib.IsMultiplicativeOn
import PrimeGapsTheory.Tactic.PaperTag

/-! # The Möbius function -/

@[expose] public section

add_to_pg "maynard" "def_mobius" ArithmeticFunction.moebius

open Nat Finset

namespace ArithmeticFunction

open Moebius

@[pg_tag "bg246" "lem_mobius_divisor_sum"]
theorem sum_divisors_moebius {d : ℕ} : ∑ e ∈ d.divisors, μ e = if d = 1 then 1 else 0 := by
  rw [← coe_mul_zeta_apply, moebius_mul_coe_zeta, one_apply]

@[pg_tag "bg246" "lem_mobius_divisor_sum"]
theorem sum_divisors_coe_moebius {α : Type*} [Ring α] {d : ℕ} :
    ∑ e ∈ d.divisors, (μ e : α) = if d = 1 then 1 else 0 := by
  simp [← Int.cast_sum, sum_divisors_moebius]

theorem sum_divisorsBetween_moebius {d e : ℕ} (h₁ : d ∣ e) (h₂ : Squarefree e) :
    ∑ r ∈ d.divisorsBetween e, μ r = if d = e then μ d else 0 := by
  have hd₀ : d ≠ 0 := ne_zero_of_dvd_ne_zero h₂.ne_zero h₁
  have h₃ {r : ℕ} (hr : r ∈ (e / d).divisors) : μ (d * r) = μ d * μ r :=
    isMultiplicative_moebius.map_mul_of_squarefree_mul <| h₂.squarefree_of_dvd <|
      (dvd_div_iff_mul_dvd h₁).mp (And.left <| by simpa using hr)
  rw [divisorsBetween, if_pos h₁, sum_image (mul_right_injective₀ hd₀).injOn]
  simp_rw +contextual [h₃]
  rw [← mul_sum, sum_divisors_moebius]
  simp only [Nat.div_eq_iff_eq_mul_right (by positivity) h₁]
  grind

theorem sum_divisorsBetween_coe_moebius {α : Type*} [Ring α]
    {d e : ℕ} (h₁ : d ∣ e) (h₂ : Squarefree e) :
    ∑ r ∈ d.divisorsBetween e, (μ r : α) = if d = e then μ d else 0 := by
  rw [← Int.cast_sum, sum_divisorsBetween_moebius h₁ h₂]

theorem sum_filter_squarefree {α : Type*} [Ring α] {s : Finset ℕ} (f : ℕ → α) :
    ∑ x ∈ s with Squarefree x, f x = ∑ x ∈ s, μ x ^ 2 * f x := by
  simp [← Int.cast_pow, moebius_sq, sum_filter]

theorem sum_filter_squarefree' {s : Finset ℕ} (f : ℕ → ℤ) :
    ∑ x ∈ s with Squarefree x, f x = ∑ x ∈ s, μ x ^ 2 * f x := by
  simp [sum_filter_squarefree]

end ArithmeticFunction
