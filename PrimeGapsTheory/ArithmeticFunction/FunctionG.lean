/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius
public import PrimeGapsTheory.ArithmeticFunction.ProdPrimePower
public import PrimeGapsTheory.ArithmeticFunction.Totient
public import PrimeGapsTheory.ForMathlib.IsMultiplicativeOn

import PrimeGapsTheory.ArithmeticFunction.Basic
import PrimeGapsTheory.Tactic.PaperTag

/-!
# The function that convolves with `ζ` to `φ`

We define the function `g` satisfying `g * ζ = φ`, in other words, `φ(n) = ∑_{d∣n} g(d)` for all
`n > 0`. This function is multiplicative, and on prime powers (`p` prime) it satisfies:
- `g(p) = p - 2`.
- `g(p^n) = p^(n-2) (p-1)^2` for `n ≥ 2`.

So on prime input, it coincides with Maynard's function `g` defined in Equation (5.22) of his paper.
This function appears in the singular-series analysis and in the `y`-variable change of basis.
-/

@[expose] public section

open Nat Finset
open ArithmeticFunction zeta Moebius

namespace ArithmeticFunction

variable {R : Type*} [CommRing R]

/-- "One step removed from totient": this function `g` satisfies `g * ζ = φ`, in other words,
`φ(n) = ∑_{d∣n} g(d)` for all `n > 0`.

This function is multiplicative, and on prime powers (`p` prime) it satisfies:
- `g(p) = p - 2`.
- `g(p^n) = p^(n-2) (p-1)^2` for `n ≥ 2`.

On prime input, it coincides with Maynard's function `g` defined in Equation (5.22) of his paper. -/
@[pg_tag "bg246" "def_g_func"]
noncomputable def detotient : ArithmeticFunction ℕ :=
  fromPrimePowers fun p n ↦ if n = 1 then p - 2 else p ^ (n - 2) * (p - 1) ^ 2

@[inherit_doc] scoped[ArithmeticFunction.detotient] notation "g" => detotient

open detotient

@[aesop safe apply] theorem isMultiplicative_detotient : (g).IsMultiplicative :=
  isMultiplicative_fromPrimePowers

@[simp] theorem detotient_one : g 1 = 1 := by decide +kernel

theorem detotient_prime {p : ℕ} (hp : p.Prime) : g p = p - 2 := fromPrimePowers_prime hp

@[simp] theorem coe_detotient_prime {p : ℕ} (hp : p.Prime) : (g p : R) = p - 2 := by
  simp [detotient_prime hp, hp.two_le]

theorem detotient_prime_pow_eq_ite {p n : ℕ} (hp : p.Prime) :
    g (p ^ n) = if n = 0 then 1 else if n = 1 then p - 2 else p ^ (n - 2) * (p - 1) ^ 2 :=
  fromPrimePowers_prime_pow hp

@[simp] theorem detotient_prime_pow {p n : ℕ} (hp : p.Prime) (hn : 2 ≤ n) :
    g (p ^ n) = p ^ (n - 2) * (p - 1) ^ 2 := by
  grind [detotient_prime_pow_eq_ite]

/-- Value on a squarefree number: `g n = ∏ p ∈ n.primeFactors, (p - 2)`. -/
theorem detotient_squarefree_eq_prod {n : ℕ} (hn : Squarefree n) :
    g n = ∏ p ∈ n.primeFactors, (p - 2) := by
  rw [← isMultiplicative_detotient.prod_primeFactors hn]
  exact prod_congr rfl fun p hp ↦ by grind [detotient_prime]

/-- Value on a squarefree number: `g n = ∏ p ∈ n.primeFactors, (p - 2)`. -/
theorem coe_detotient_squarefree_eq_prod {n : ℕ} (hn : Squarefree n) :
    (g n : R) = ∏ p ∈ n.primeFactors, (p - 2 : R) := by
  rw [← isMultiplicative_detotient.prod_primeFactors hn, cast_prod]
  exact prod_congr rfl fun p hp ↦ by grind [coe_detotient_prime]

theorem detotient_eq_zero_iff {n : ℕ} (hn : Squarefree n) : g n = 0 ↔ 2 ∣ n := by
  rw [detotient_squarefree_eq_prod hn, prod_eq_zero_iff]
  simp_rw [mem_primeFactors, Nat.sub_eq_zero_iff_le, eq_true hn.ne_zero, and_true]
  refine ⟨fun ⟨p, ⟨hp, hpn⟩, hp2⟩ ↦ by grind [hp.two_le], fun h ↦ ⟨2, ?_⟩⟩
  grind [prime_two]

/-- For odd `n`, `0 < g n`. -/
theorem detotient_pos_of_odd {n : ℕ} (hn : Odd n) : 0 < g n := by
  rw [isMultiplicative_detotient.multiplicative_factorization _ (by grind)]
  refine Finset.prod_pos fun p hp ↦ pos_of_ne_zero ?_
  rw [Nat.support_factorization, Nat.mem_primeFactors] at hp
  have hp2 : p ≠ 2 := by grind [Odd.not_two_dvd_nat]
  obtain ⟨hpp, hpdvd, _⟩ := hp
  simp_rw [detotient_prime_pow_eq_ite hpp]
  simp [ite_eq_iff]
  grind [hpp.two_le]

theorem coe_detotient_eq_totient_mul_moebius : g = totient * μ := by
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (by aesop) _ (by aesop)).mpr fun p n hp ↦ ?_
  rw [mul_apply_prime_pow hp]
  obtain _ | _ | n := n
  · simp
  · simp [hp, Nat.sum_antidiagonal_succ, moebius_apply_prime, totient_prime]
    grind [hp.two_le]
  rw [← Nat.sum_antidiagonal_swap, Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    sum_range_succ', sum_range_succ']
  simp [hp, moebius_apply_prime, moebius_apply_prime_pow, totient_prime_pow_succ, hp.one_le]
  ring

@[simp] theorem detotient_mul_zeta : g * ζ = totient := by
  refine natCoe_injective (R := ℤ) ?_
  simp [coe_detotient_eq_totient_mul_moebius, mul_assoc]

@[simp] theorem zeta_mul_detotient : ζ * g = totient := by grind [detotient_mul_zeta]

theorem sum_divisors_detotient {n : ℕ} : ∑ d ∈ n.divisors, g d = φ n := by
  rw [← zeta_mul_apply, zeta_mul_detotient, totient_apply]

end ArithmeticFunction
