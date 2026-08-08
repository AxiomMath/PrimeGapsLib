/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Notation.Indicator
public import Mathlib.Data.Nat.Prime.Defs
public import Mathlib.Data.Real.Basic

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Prime indicator

Defines the real-valued indicator of the natural primes used by the Draft sieve estimates.

## Main definitions

* `primeIndicator`: The real-valued indicator function of the set of primes.
-/

@[expose] public section

namespace PrimeGaps

/-- Maynard `not:standard`'s prime-indicator function `χ_𝒫(n) = 1` if `n` is prime and `0`
otherwise. -/
@[pg_tag "bg246" "not_standard"]
noncomputable def primeIndicator : ℕ → ℝ :=
  {p : ℕ | p.Prime}.indicator (1 : ℕ → ℝ)

/-- `primeIndicator n = 1` when `n` is prime, and `0` otherwise. -/
lemma primeIndicator_apply (n : ℕ) : primeIndicator n = if n.Prime then 1 else 0 := by
  simp [primeIndicator, Set.indicator_apply]

end PrimeGaps
