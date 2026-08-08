/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal


/-! # Infinite sums over ℝ -/

@[expose] public section

open Filter Topology Finset

theorem hasSum_nat_telescope {f : ℕ → ℝ} (hf : Antitone f) (hf₀ : Tendsto f atTop (𝓝 0)) :
    HasSum (fun n ↦ f n - f (n + 1)) (f 0) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg (by aesop)]
  convert hf₀.const_sub (f 0)
  · exact sum_range_sub' _ _
  · rw [sub_zero]
