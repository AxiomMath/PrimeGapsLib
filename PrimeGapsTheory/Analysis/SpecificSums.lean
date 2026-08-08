/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ForMathlib.Topology.Algebra.InfiniteSum.ENNReal

import Mathlib.Analysis.SpecificLimits.Basic


/-! # Specific (infinite) sums

Closed evaluations of two elementary telescoping series.

## Main results

* `hasSum_one_div_add_one_mul_add_two`: `∑_{n ≥ 0} 1 / ((n + 1)(n + 2)) = 1`.
* `hasSum_one_div_mul_sub_one`: `∑_{n ≥ 0} 1 / (n(n - 1)) = 1`.
-/

@[expose] public section

open Finset

theorem hasSum_one_div_add_one_mul_add_two :
    HasSum (fun n : ℕ ↦ (1 / ((n + 1) * (n + 2)) : ℝ)) 1 := by
  convert hasSum_nat_telescope (fun _ _ h ↦
    one_div_le_one_div_of_le (by positivity) (by grw [h]))
    tendsto_one_div_add_atTop_nhds_zero_nat with n
  · grind
  · simp

theorem hasSum_one_div_mul_sub_one : HasSum (fun n : ℕ ↦ (1 / (n * (n - 1)) : ℝ)) 1 := by
  rw [← hasSum_nat_add_iff' 2]
  convert hasSum_one_div_add_one_mul_add_two using 2
  · rfl
  · grind
  · simp [sum_range_succ]
