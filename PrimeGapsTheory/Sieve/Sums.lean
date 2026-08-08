/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW

import PrimeGapsTheory.Tactic.PaperTag

/-! # Sums `S₁` and `S₂` and related definitions

Setup for Maynard's proof of bounded gaps between primes: the sieve weight `w n` attached to an
admissible tuple `h : Fin k → ℕ` with coefficients `l`, together with the two principal sums `S₁`
and `S₂` over the integers `n ∈ (N, 2N]` lying in a fixed residue class `n ≡ v₀ [MOD W N]`.

## Main definitions

* `PrimeGaps.weight` — the sieve weight `w n`, with scoped notation `w`.
* `PrimeGaps.S₁` — the denominator sum `∑_n w_n`.
* `PrimeGaps.S₂` — the numerator sum `∑_n #{i : n + h i prime} * w_n`.
* `PrimeGaps.S₂m` — the `m`-th component of `S₂`.

## Main results

* `PrimeGaps.sum_S₂m_eq_S₂` — `S₂` decomposes as the sum `∑_m S₂m`.
-/

@[expose] public section

open Finset
open scoped PrimeGaps.sieveModulus

namespace PrimeGaps

/-- The weight `w := (∑_{∀ i, d_i ∣ n + h_i}, λ_d) ^ 2`. -/
@[pg_tag "bg246" "def_weight"]
def weight {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ) (n : ℕ) : ℝ :=
  (∑ d ∈ Fintype.piFinset fun i ↦ (n + h i).divisors, l d) ^ 2

/-- The notation `w` denotes the sieve weight `weight`. -/
@[pg_tag "bg246" "def_weight" "The weight `w := (∑_{∀ i, d_i ∣ n + h_i}, λ_d) ^ 2`."]
scoped notation "w" => weight

/-- The denominator sum `S₁ = ∑_n w_n`, taken over the integers
`n ∈ (N, 2N]` in the fixed residue class `n ≡ v₀ [MOD W N]`. -/
@[pg_tag "bg246" "def_S1"]
noncomputable def S₁ {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ) (N : ℕ) (w₀ : ZMod (W N)) : ℝ :=
  ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀, weight h l n

/-- The numerator sum `S₂ = ∑_n #{i : n + h i prime} * w_n`, weighting each `n`
(over the same range and residue class as `S₁`) by the number of indices `i`
for which `n + h i` is prime. By `sum_S₂m_eq_S₂` it splits as `∑_m S₂m`. -/
@[pg_tag "bg246" "def_S2"]
noncomputable def S₂ {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ) (N : ℕ) (w₀ : ZMod (W N)) : ℝ :=
  ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀, #{i | (n + h i).Prime} * weight h l n

/-- The `m`-th piece of `S₂`: `S₂m m = ∑_n w_n · 𝟙[n + h m prime]`, summing the
weight `w_n` (over the same range and residue class as `S₁`) only over those
`n` for which `n + h m` is prime. -/
@[pg_tag "bg246" "def_S2m"]
noncomputable def S₂m {k : ℕ} (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ)
    (N : ℕ) (w₀ : ZMod (W N)) (m : Fin k) : ℝ :=
  ∑ n ∈ Ioc N (2 * N) with (n : ℕ) = w₀, (if (n + h m).Prime then 1 else 0) * weight h l n

variable {k : ℕ} {h : Fin k → ℕ} {l : (Fin k → ℕ) → ℝ} {n N : ℕ} {w₀ : ZMod (W N)}

@[pg_tag "bg246" "lem_wn_nonneg"]
lemma w_nonneg : 0 ≤ w h l n := sq_nonneg _

@[pg_tag "bg246" "lem_S2_decomp"]
theorem sum_S₂m_eq_S₂ : ∑ m, S₂m h l N w₀ m = S₂ h l N w₀ := by
  simp_rw +singlePass [S₂, S₂m, sum_comm]
  refine sum_congr rfl fun n hn ↦ ?_
  rw [card_eq_sum_ones, sum_filter, Nat.cast_sum, sum_mul]
  norm_cast

end PrimeGaps
