/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.NumberTheory.PrimeCounting

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Counting primes in an interval

We count the primes in `(x, y]`, both in total (`Nat.primeCountingIoc`) and in a fixed residue
class modulo `q` (`ZMod.primeCountingIoc`), and package the discrepancy between the two into the
error term `Nat.primeCountingIocError` of the prime number theorem in an interval.
-/

@[expose] public section

open Finset

namespace Nat

/-- Number of primes in the interval `(x, y]`. -/
@[pg_tag "bg246" "not_XN"]
def primeCountingIoc (x y : ℕ) : ℕ := #{n ∈ Ioc x y | n.Prime}

/-- The primes at most `y` that are not at most `x` are exactly the primes in `(x, y]`. -/
theorem primesLE_sdiff_eq_filter_Ioc (x y : ℕ) :
    y.primesLE \ x.primesLE = {n ∈ Ioc x y | n.Prime} := by
  ext p
  by_cases hp : p.Prime <;>
    simp only [mem_sdiff, mem_primesLE, mem_filter, mem_Ioc, hp, and_true, and_false,
      not_false_eq_true]
  omega

/-- Counting the primes in `(x, y]` and then those at most `x` counts the primes at most `y`. -/
theorem primeCountingIoc_add_primeCounting {x y : ℕ} (h : x ≤ y) :
    primeCountingIoc x y + x.primeCounting = y.primeCounting := by
  simpa only [primeCountingIoc, ← primesLE_sdiff_eq_filter_Ioc, primesLE_card_eq_primeCounting]
    using card_sdiff_add_card_eq_card (primesLE_mono h)

/-- The number of primes in `(x, y]` is the difference of the prime counting function at the
endpoints. -/
theorem primeCountingIoc_eq_sub (x y : ℕ) :
    primeCountingIoc x y = y.primeCounting - x.primeCounting := by
  rcases le_or_gt x y with h | h
  · have := primeCountingIoc_add_primeCounting h
    omega
  · simp [primeCountingIoc, Ioc_eq_empty_of_le h.le,
      Nat.sub_eq_zero_of_le (monotone_primeCounting h.le)]

/-- `primeCountingIoc_eq_sub` in a ring, where the subtraction is not truncated. -/
theorem cast_primeCountingIoc {R : Type*} [AddGroupWithOne R] {x y : ℕ} (h : x ≤ y) :
    (primeCountingIoc x y : R) = y.primeCounting - x.primeCounting := by
  rw [eq_sub_iff_add_eq, ← Nat.cast_add, primeCountingIoc_add_primeCounting h]

end Nat

/-- Number of primes in the interval `(x, y]` that are congruent to `a` modulo `q`. -/
def ZMod.primeCountingIoc (x y : ℕ) {q : ℕ} (a : ZMod q) : ℕ :=
  #{n ∈ Ioc x y | (n : ℕ).Prime ∧ n = a}

@[inherit_doc] scoped[PrimeGaps] notation "π(" x:max ", " y:max ")" => Nat.primeCountingIoc x y
@[inherit_doc] scoped[PrimeGaps] notation "π(" x:max ", " y:max "; " q:max ", " a:max ")" =>
  ZMod.primeCountingIoc x y (q := q) a

open PrimeGaps

namespace Nat

/-- Error term for the prime number theorem in an interval. -/
@[pg_tag "bg246" "not_error"]
noncomputable def primeCountingIocError (x y q : ℕ) : ℝ :=
  1 + ⨆ a : (ZMod q)ˣ, |(π(x, y; q, a) - π(x, y) / q.totient : ℝ)|

end Nat

@[inherit_doc] scoped[PrimeGaps] notation "E(" x:max ", " y:max "; " q:max ")" =>
  Nat.primeCountingIocError x y q

namespace Nat

/-- The supremum inside `primeCountingIocError` is a supremum of nonnegative reals,
over the finite index `(ZMod q)ˣ`, hence bounded above. -/
theorem primeCountingIocError_bddAbove (x y q : ℕ) [NeZero q] :
    BddAbove (Set.range fun a : (ZMod q)ˣ ↦ |(π(x, y; q, a) - π(x, y) / q.totient : ℝ)|) :=
  Set.Finite.bddAbove (Set.finite_range _)

theorem one_le_primeCountingIocError (x y q : ℕ) : 1 ≤ primeCountingIocError x y q :=
  le_add_of_nonneg_right <| Real.iSup_nonneg fun _ ↦ abs_nonneg _

theorem primeCountingIocError_nonneg (x y q : ℕ) : 0 ≤ primeCountingIocError x y q :=
  zero_le_one.trans (one_le_primeCountingIocError x y q)

/-- The comparison-with-main-term bound: for every unit residue `a`, the discrepancy
`|π(x, y; q, a) - π(x, y) / φ(q)|` is at most `primeCountingIocError x y q - 1`. -/
theorem abs_sub_div_le_primeCountingIocError_sub_one (x y q : ℕ) [NeZero q] (a : (ZMod q)ˣ) :
    |(π(x, y; q, a) - π(x, y) / q.totient : ℝ)| ≤ primeCountingIocError x y q - 1 := by
  simpa [primeCountingIocError] using le_ciSup (primeCountingIocError_bddAbove x y q) a

end Nat
