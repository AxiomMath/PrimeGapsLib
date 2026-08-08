/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import PrimeGapsCert.Gap246.Kernel.Core

/-! # Range facts about the packed label accessors and the factorial folds -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

/-- The packed coefficient-sign field is one bit. -/
theorem labelSign_lt_two (field : ℕ) : cert246Data.labelSign field < 2 := by
  unfold cert246Data.labelSign
  exact Nat.lt_of_le_of_lt Nat.and_le_right (Nat.lt_succ_self 1)

/-- The dependency-free factorial fold agrees with the mathematical factorial. -/
theorem factorialFold_eq_factorial (n : ℕ) : cert246Data.factorialFold n = n ! := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      have hstep : cert246Data.factorialFold (n + 1) =
        Nat.mul (Nat.succ n) (cert246Data.factorialFold n) := rfl
      rw [hstep, inductionHypothesis, Nat.mul_eq, Nat.factorial_succ]

/-- The dependency-free descending-factorial fold agrees with the mathematical one. -/
theorem descFactorialFold_eq_descFactorial (n k : ℕ) :
    cert246Data.descFactorialFold n k = Nat.descFactorial n k := by
  induction k with
  | zero => rfl
  | succ k inductionHypothesis =>
      have hstep : cert246Data.descFactorialFold n (k + 1) =
        Nat.mul (Nat.sub n k) (cert246Data.descFactorialFold n k) := rfl
      rw [hstep, inductionHypothesis, Nat.mul_eq, Nat.sub_eq, Nat.descFactorial_succ]

end PrimeGaps.Gap246
