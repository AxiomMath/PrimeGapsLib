/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW
public import PrimeGapsTheory.Sieve.SieveTruncation

import PrimeGapsTheory.Tactic.PaperTag

/-! # Size of the sieve support factor

The sieve support factor `R² · W N` is eventually bounded by `N ^ (1 / 2 - ε)`, for any `ε` below
the exponent budget `1 / 2 - (θ - 2δ)`.

## Main results

* `PrimeGaps.sieve_support_le`: eventually `R ^ 2 * W N ≤ N ^ (1 / 2 - ε)`.
-/

@[expose] public section

open PrimeGaps Real Filter
open scoped PrimeGaps.sieveModulus PrimeGaps.sieveTruncation

private lemma sieveTruncation_sq {N : ℕ} {δ θ : ℝ} : R ^ 2 = N ^ (θ - 2 * δ) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  grind

attribute [local grind .] exp_one_gt_two sub_nonneg log_nonneg le_log_iff_exp_le in
private lemma eventually_W_le_rpow {γ : ℝ} (hγ : 0 < γ) : ∀ᶠ N in atTop, (W N : ℝ) ≤ N ^ γ := by
  have hlittleReal : (fun x : ℝ ↦ (log x) ^ 2) =o[atTop] fun x : ℝ ↦ x ^ γ := by
    simpa using isLittleO_log_rpow_rpow_atTop (r := 2) (s := γ) hγ
  filter_upwards [lem_W_size, hlittleReal.natCast_atTop.eventuallyLE,
    eventually_ge_atTop ⌈rexp 1⌉₊]
    with N hWsize hlo hN
  rw [Nat.ceil_le] at hN
  simp only [norm_pow, norm_eq_abs, sq_abs] at hlo
  grw [hWsize, log_le_sub_one_of_pos (log_pos _), (_ : log N - 1 ≤ log N), hlo]
  all_goals grind [rpow_nonneg]

namespace PrimeGaps

/-- Eventually (for all sufficiently large `N`) the sieve support factor
`R² · W` is bounded by `N^(1/2 - ε)`, whenever `ε` lies below the exponent
budget `1/2 - (θ - 2δ)`. Here `R = sieveTruncation N δ θ = N^(θ/2 - δ)` and
`W = W N` is the primorial `∏_{p ≤ log log log N} p`. -/
@[pg_tag "bg246" "lem_R2W_below_N_half_minus_eps"]
theorem sieve_support_le {θ δ ε : ℝ} (hε : ε < 1 / 2 - (θ - 2 * δ)) :
    ∀ᶠ N in atTop, R ^ 2 * W N ≤ N ^ (1 / 2 - ε) := by
  set γ : ℝ := 1 / 2 - ε - (θ - 2 * δ) with hγdef
  have hγ : 0 < γ := by grind
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 (eventually_W_le_rpow hγ)
  refine eventually_atTop.mpr ⟨max N₀ 1, fun N hN ↦ ?_⟩
  rw [sieveTruncation_sq, show (1 : ℝ) / 2 - ε = θ - 2 * δ + γ from
    (add_sub_cancel (θ - 2 * δ) (1 / 2 - ε)).symm]
  grw [Real.rpow_add (Nat.cast_pos.mpr <| one_pos.trans_le ((le_max_right N₀ 1).trans hN)),
    hN₀ N ((le_max_left N₀ 1).trans hN)]

end PrimeGaps
