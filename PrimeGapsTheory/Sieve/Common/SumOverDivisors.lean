/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.GCD.Basic

/-!
# Least-common-multiple divisibility

Relates divisibility by coordinatewise least common multiples to simultaneous divisibility.

## Main results

* `cond_lcm_iff`: Characterizes coordinatewise divisibility by least common multiples.
-/

@[expose] public section

namespace PrimeGaps.SumOverDivisors

/-- Per-index divisibility by both `d i` and `e i` is equivalent to divisibility by
`Nat.lcm (d i) (e i)`.
-/
lemma cond_lcm_iff {k : ℕ} (h : Fin k → ℕ) (n : ℕ) (d e : Fin k → ℕ) :
    ((∀ i, d i ∣ n + h i) ∧ (∀ i, e i ∣ n + h i)) ↔
      (∀ i, Nat.lcm (d i) (e i) ∣ n + h i) := by
  simp [← forall_and, Nat.lcm_dvd_iff]

end PrimeGaps.SumOverDivisors

end
