/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Defs

import PrimeGapsTheory.ForMathlib.Algebra.BigOperators.Finsupp.Basic


/-! # Arithmetic Function from Prime Powers

We define multiplicative arithmetic functions from specifying their values on prime powers.
-/

@[expose] public section

open Nat

namespace ArithmeticFunction
variable {R : Type*} [CommMonoidWithZero R]

/-- Construct a multiplicative arithmetic function from specifying its values on prime powers. -/
def fromPrimePowers (f : ℕ → ℕ → R) : ArithmeticFunction R where
  toFun n := if n = 0 then 0 else n.factorization.prod f
  map_zero' := if_pos rfl

variable {f : ℕ → ℕ → R}

@[simp] theorem fromPrimePowers_one : fromPrimePowers f 1 = 1 := by
  simp [fromPrimePowers]

theorem fromPrimePowers_prime_pow {p n : ℕ} (hp : p.Prime) :
    fromPrimePowers f (p ^ n) = if n = 0 then 1 else f p n := by
  split_ifs with hn
  · simp [hn]
  simp [fromPrimePowers, hp, hp.ne_zero, Finsupp.prod_single_index_of_ne hn]

@[simp] theorem fromPrimePowers_prime {p : ℕ} (hp : p.Prime) : fromPrimePowers f p = f p 1 := by
  simpa using fromPrimePowers_prime_pow hp (n := 1)

@[simp] theorem fromPrimePowers_prime_pow_succ {p n : ℕ} (hp : p.Prime) :
    fromPrimePowers f (p ^ (n + 1)) = f p (n + 1) := by
  simp [fromPrimePowers_prime_pow hp]

@[aesop safe apply]
theorem isMultiplicative_fromPrimePowers : IsMultiplicative (fromPrimePowers f) := by
  refine ⟨by simp, fun {m n} hmn ↦ ?_⟩
  simp_rw [fromPrimePowers, coe_mk]
  by_cases! hmn₀ : m = 0 ∨ n = 0
  · aesop
  obtain ⟨hm₀, hn₀⟩ := hmn₀
  simp_rw [mul_eq_zero, hm₀, hn₀, false_or, ite_false, factorization_mul hm₀ hn₀]
  exact Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors _

end ArithmeticFunction
