/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.Tau
public import PrimeGapsTheory.Arithmetic.Totient.Lcm

import PrimeGapsTheory.ArithmeticFunction.Estimates
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Totient and divisor-sum identities

Divisor-sum identities for the totient, Möbius, and divisor functions on squarefree integers.

## Main results

* `totient_eq_sum_divisors_g`: The totient as a divisor sum of `g`.
* `inv_d_totient_le`: An upper bound for the reciprocal totient weight.
-/

@[expose] public section

open scoped Finset
open scoped ArithmeticFunction.detotient

open ArithmeticFunction Finset

namespace PrimeGaps

/-- For a positive squarefree `n`, its real-valued totient is the product of `p - 1`
over its prime factors. -/
lemma totient_eq_prod_sub_one (n : ℕ) (hn : 0 < n) (hsq : Squarefree n) :
    (n.totient : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
  rw [Nat.totient_squarefree_prod hsq hn, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]
  simp

/-- A squarefree natural number, cast to `ℝ`, is the product of its prime factors. -/
lemma squarefree_eq_prod_primes (n : ℕ) (hsq : Squarefree n) :
    (n : ℝ) = ∏ p ∈ n.primeFactors, (p : ℝ) := by
  rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]

end PrimeGaps

namespace Nat

/-- `n ≤ φ(n) · d(n)`, obtained by bounding each term in `∑_{d ∣ n} φ(d) = n` by `φ(n)`. -/
lemma le_totient_mul_card_divisors (n : ℕ) : n ≤ Nat.totient n * #n.divisors := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  conv_lhs => rw [← Nat.sum_totient n]
  calc (n.divisors.sum Nat.totient) ≤ ∑ d ∈ n.divisors, Nat.totient n :=
        Finset.sum_le_sum fun d hd ↦ Nat.le_of_dvd
          (Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn))
          (Nat.totient_dvd_of_dvd (Nat.dvd_of_mem_divisors hd))
    _ = Nat.totient n * #n.divisors := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- For positive `n`, the average divisor contribution bounds `n / d(n)` by `φ(n)`. -/
lemma div_card_le_totient (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / (#n.divisors : ℝ) ≤ (n.totient : ℝ) := by
  have hn0 : 0 < n := hn
  have hcardpos : 0 < #n.divisors := Finset.card_pos.mpr ⟨n, Nat.mem_divisors_self n hn0.ne'⟩
  have hcardR : (0 : ℝ) < (#n.divisors : ℝ) := by exact_mod_cast hcardpos
  rw [div_le_iff₀ hcardR]
  exact_mod_cast Nat.le_totient_mul_card_divisors n

/-- The Euler totient `φ(n)` is the divisor sum `∑_{u ∣ n} g(u)`, as an equality of integers. -/
@[pg_tag "bg246" "lem_phi_g_convolution"]
theorem totient_eq_sum_divisors_g (n : ℕ) :
    (Nat.totient n : ℤ) = ∑ u ∈ n.divisors, (g u : ℤ) :=
  mod_cast ArithmeticFunction.sum_divisors_detotient.symm

open scoped ArithmeticFunction ArithmeticFunction.zeta

/-- For `0 < d`, `1 / (d * φ d) ≤ τ 2 d / d ^ 2`. -/
@[pg_tag "bg246" "lem_phi_lower_sf"]
theorem inv_d_totient_le (d : ℕ) (hd : 0 < d) :
    (1 : ℚ) / ((d : ℚ) * (Nat.totient d : ℚ)) ≤ ((τ 2) d : ℚ) / (d : ℚ) ^ 2 := by
  have hint := ArithmeticFunction.le_tau₂_mul_totient (n := d)
  have hdpos : (0 : ℚ) < d := by exact_mod_cast hd
  have htot_pos : 0 < Nat.totient d := Nat.totient_pos.mpr hd
  have htotq : (0 : ℚ) < Nat.totient d := by exact_mod_cast htot_pos
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, sq]
  have hcast : (d : ℚ) ≤ ((τ 2) d : ℚ) * (Nat.totient d : ℚ) := by exact_mod_cast hint
  calc (d : ℚ) * d ≤ (((τ 2) d : ℚ) * Nat.totient d) * d :=
        mul_le_mul_of_nonneg_right hcast hdpos.le
    _ = ((τ 2) d : ℚ) * (d * Nat.totient d) := by ring

end Nat
