/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.ArithmeticFunction.Moebius


/-! # Basic facts about arithmetic functions -/

@[expose] public section

open Nat Finset

namespace ArithmeticFunction

theorem mul_apply_prime_pow {R : Type*} [Semiring R]
    {f g : ArithmeticFunction R} {p n : ℕ} (hp : p.Prime) :
    (f * g) (p ^ n) = ∑ k ∈ antidiagonal n, f (p ^ k.1) * g (p ^ k.2) := by
  rw [mul_apply, sum_divisorsAntidiagonal (f · * g ·), divisors_prime_pow hp, sum_map,
    Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr! 3 with i hi
  refine Nat.div_eq_of_eq_mul_left (pow_pos hp.pos _) ?_
  simp [← pow_add, mem_range_succ_iff.mp hi]

theorem natCoe_injective {R : Type*} [AddMonoidWithOne R] [CharZero R] :
    Function.Injective ((↑) : ArithmeticFunction ℕ → ArithmeticFunction R) := fun _ _ h ↦
  ext fun n ↦ Nat.cast_injective congr($h n)

attribute [aesop safe apply] IsMultiplicative.natCast IsMultiplicative.intCast isMultiplicative_one
  isMultiplicative_finsetProd IsMultiplicative.pow IsMultiplicative.mul isMultiplicative_zeta
  IsMultiplicative.ppow IsMultiplicative.pmul IsMultiplicative.pdiv isMultiplicative_id
  isMultiplicative_pow isMultiplicative_sigma IsMultiplicative.prodPrimeFactors
  isMultiplicative_moebius

end ArithmeticFunction
