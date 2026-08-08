/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

import PrimeGapsTheory.Tactic.PaperTag

/-! # The sieve truncation parameter `R`

The truncation level `R = N ^ (θ / 2 - δ)` at which the sieve weights are cut off.

## Main definitions

* `PrimeGaps.sieveTruncation`: the parameter `R`, with scoped notation `R`.

## Main results

* `PrimeGaps.two_le_rpow_of_exp_log_two_div_le`: `2 ≤ x ^ s` once `exp (log 2 / s) ≤ x`.
-/

@[expose] public section

open Real

namespace PrimeGaps

/-- Given real numbers `N` (typically large), `δ` (typically small), and `θ` (typically the level of
distribution of some set), the *sieve truncation parameter `R`* is defined to be
`N ^ (θ / 2 - δ)`. -/
@[pg_tag "bg246" "def_R"]
noncomputable abbrev sieveTruncation (N : ℕ) (δ θ : ℝ) : ℝ := N ^ (θ / 2 - δ)

set_option hygiene false in
/-- Given real numbers `N` (typically large), `δ` (typically small), and `θ` (typically the level of
distribution of some set), the *sieve truncation parameter `R`* is defined to be
`N ^ (θ / 2 - δ)`. -/
@[pg_tag "bg246" "def_R"]
scoped[PrimeGaps.sieveTruncation] notation "R" => sieveTruncation N δ θ

/-- `2 ≤ x ^ s` once `exp (log 2 / s) ≤ x`, for a positive exponent `s`. -/
theorem two_le_rpow_of_exp_log_two_div_le {x s : ℝ} (hs : 0 < s)
    (hx : rexp (Real.log 2 / s) ≤ x) : (2 : ℝ) ≤ x ^ s := by
  have hxpos : (0 : ℝ) < x := (Real.exp_pos _).trans_le hx
  refine (Real.log_le_log_iff (by positivity) (Real.rpow_pos_of_pos hxpos s)).mp ?_
  rw [Real.log_rpow hxpos]
  exact (div_le_iff₀' hs).mp ((Real.le_log_iff_exp_le hxpos).mpr hx)

end PrimeGaps
