/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.Simplex
public import PrimeGapsTheory.ArithmeticFunction.LYTransform.Basic
import PrimeGapsTheory.Tactic.PaperTag

/-! # Maynard sieve weights `λ`

This file defines the sieve weights `λ_{d₁,…,dₖ}` from Maynard's work on bounded gaps between
primes. They are built from a function `F : ℝᵏ → ℝ` (typically supported on the standard
`k`-simplex).

## Main definitions

* `PrimeGaps.y₀`: the transformed coefficients `y_{r₁,…,rₖ}` cut out by `F`.
* `PrimeGaps.l₀`: the weight `λ_{d₁,…,dₖ}` obtained from `y₀`.
-/

@[expose] public section

open Nat ArithmeticFunction Moebius Finset

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

namespace PrimeGaps

/-- The transformed sieve coefficients determined by `F`, restricted to permissible tuples. -/
@[pg_tag "bg246" "def_y_0"]
noncomputable def y₀ {k : ℕ} (R : ℝ) (W : ℕ) (F : ES(ℝ, k) → ℝ) : (Fin k → ℕ) →₀ ℝ :=
  .indicator (permissibleSupport k ⌊R⌋₊ W) fun r _ ↦
    F <| WithLp.toLp 2 fun i ↦ Real.log (r i) / Real.log R

/-- Weights `λ_{d₁,…,dₖ}`, defined in terms of
* real numbers `N` (typically large), `δ` (typically small), and `θ` (typically the level of
  distribution of some set)
* a function `F : ℝᵏ → ℝ` (typically supported on the standard `k`-simplex)
* natural numbers `d₁,…,dₖ` (typically with `∏ᵢ dᵢ` coprime to `W`)
-/
@[pg_tag "bg246" "lem_lambda_0_is_lambda_y0"]
noncomputable def l₀ {k : ℕ} (R : ℝ) (W : ℕ) (F : ES(ℝ, k) → ℝ) :
    (Fin k → ℕ) →₀ ℝ := yToL <| y₀ R W F

variable {k : ℕ} {R : ℝ} {W : ℕ} {F : ES(ℝ, k) → ℝ} {d r : Fin k → ℕ}

@[pg_tag "bg246" "def_y_0"]
theorem y₀_apply : y₀ R W F r = if r ∈ permissibleSupport k ⌊R⌋₊ W then
    F <| WithLp.toLp 2 fun i ↦ Real.log (r i) / Real.log R else 0 := by
  rw [y₀, Finsupp.indicator_apply, dite_eq_ite]

@[pg_tag "bg246" "lem_y_0_support"]
theorem hasPermissibleSupport_y₀ : (y₀ R W F).HasPermissibleSupport ⌊R⌋₊ W :=
  Finsupp.support_indicator_subset ..

@[pg_tag "bg246" "lem_lambda_0_permissible_support"]
theorem hasPermissibleSupport_l₀ : (l₀ R W F).HasPermissibleSupport ⌊R⌋₊ W :=
  hasPermissibleSupport_y₀.yToL

@[pg_tag "bg246" "def_lambda_from_F"]
theorem l₀_apply : l₀ R W F d = (∏ i, μ (d i) * d i) *
    ∑ r ∈ permissibleSupport k ⌊R⌋₊ W with ∀ i, d i ∣ r i, 1 / (∏ i, φ (r i)) *
      F (WithLp.toLp 2 fun i ↦ Real.log (r i) / Real.log R) := by
  rw [l₀, yToL_apply hasPermissibleSupport_y₀]
  refine congrArg₂ _ rfl ?_
  rw [Finsupp.sum_of_support_subset _ hasPermissibleSupport_y₀ _ (by simp)]
  simp +contextual [y₀_apply, sum_filter, div_eq_mul_inv, mul_comm]

end PrimeGaps
