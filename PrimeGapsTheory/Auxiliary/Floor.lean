/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.RCLike.Basic
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Floor inequalities

Floor inequalities for real parameters near positive integers.

## Main results

* `lem_floor_ineq`: A strict real inequality gives a lower bound on a natural floor.
* `lem_floor_rho`: The floor of a perturbed real parameter is locally constant.
-/

@[expose] public section

namespace PrimeGaps

/-- If `ρ > 0` and `(m : ℝ) > ρ`, then `m ≥ Nat.floor (ρ + 1)`. -/
@[pg_tag "bg246" "lem_floor_ineq"]
theorem lem_floor_ineq (ρ : ℝ) (hρ : ρ > 0) (m : ℕ) (hm : (m : ℝ) > ρ) : m ≥ ⌊ρ + 1⌋₊ := by
  rw [ge_iff_le, ← Nat.lt_succ_iff, Nat.floor_lt (by linarith)]
  push_cast
  linarith

/-- For `x ∈ (r - 1, r]` with `r ≥ 1`, there exists a positive `ε₀`
such that for all `ε ∈ (0, ε₀)`, `⌊(x - ε) + 1⌋ = r`. -/
@[pg_tag "bg246" "lem_floor_rho"]
theorem lem_floor_rho (x : ℝ) (r : ℕ) (hr : 0 < r) (hx_lo : (r : ℝ) - 1 < x) (hx_hi : x ≤ r) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ⌊(x - ε) + 1⌋₊ = r := by
  have hr' : (1 : ℝ) ≤ r := by exact_mod_cast hr
  refine ⟨(x - (r - 1 : ℝ)) / 2, by linarith, fun ε hε_pos hε_lt ↦ ?_⟩
  rw [Nat.floor_eq_iff (by linarith)]
  exact ⟨by linarith, by linarith⟩

end PrimeGaps
