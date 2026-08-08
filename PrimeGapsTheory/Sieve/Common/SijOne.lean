/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# The all-one off-diagonal contribution

Both moments reduce their `s ≡ 1` contribution by one and the same pointwise identity: on a
tuple `u` all of whose entries are squarefree the Möbius-square weight `∏ᵢ μ(uᵢ)² / w(uᵢ)`
collapses to `1 / ∏ᵢ w(uᵢ)`, and off that support the `y`-functional vanishes, so both sides
are zero. The identity is recorded here once, for an arbitrary per-coordinate weight `w`, an
arbitrary `y`-functional supported on squarefree tuples, and an arbitrary summation guard.

## Main results

* `PrimeGaps.mul_tsum_mobiusSq_weight_mul_self`: the shared `s ≡ 1` identity.
-/

@[expose] public section

namespace PrimeGaps

open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

/-- Folding the Möbius-square weight into the square of a `y`-functional: for any weight
`w : ℕ → ℝ`, any guard `P` and any `y` vanishing on tuples with a non-squarefree entry,

`∑' u, [P u] (∏ᵢ μ(uᵢ)²/w(uᵢ)) * y u * y u = ∑' u, [P u] (y u)² / ∏ᵢ w(uᵢ)`,

up to a common scalar prefactor `c`. No squarefree hypothesis on `u` is needed: where the
Möbius weight fails to be `1`, the functional `y` is already zero. -/
theorem mul_tsum_mobiusSq_weight_mul_self {k : ℕ} (c : ℝ) (w : ℕ → ℝ) (y : (Fin k → ℕ) → ℝ)
    (P : (Fin k → ℕ) → Prop) [DecidablePred P]
    (hy : ∀ u : Fin k → ℕ, (∀ i, Squarefree (u i)) ∨ y u = 0) :
    c * (∑' u : Fin k → ℕ, if P u then
            (∏ i, (μ (u i) : ℝ) ^ 2 / w (u i)) * y u * y u
          else 0)
      =
    c * (∑' u : Fin k → ℕ, if P u then y u ^ 2 / (∏ i, w (u i)) else 0) := by
  congr 1
  refine tsum_congr fun u ↦ ?_
  by_cases h : P u
  · rw [if_pos h, if_pos h]
    rcases hy u with hsq | hzero
    · rw [Finset.prod_div_distrib, Finset.prod_eq_one fun i _ ↦ by
        exact_mod_cast moebius_sq_eq_one_of_squarefree (hsq i)]
      ring
    · rw [hzero]; ring
  · simp [h]

end PrimeGaps
