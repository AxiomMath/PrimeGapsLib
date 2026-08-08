/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Summable


/-! # Infinite sums over ℝ and exp/log -/

@[expose] public section

namespace Real

theorem tprod_one_add_le_rexp_tsum {α : Type*} {f : α → ℝ} (hf₀ : ∀ i, 0 ≤ f i)
    (hf : Summable f) : ∏' i, (1 + f i) ≤ rexp (∑' i, f i) := by
  obtain _ | _ := isEmpty_or_nonempty α
  · simp
  exact le_of_tendsto_of_tendsto' (Real.multipliable_one_add_of_summable hf).hasProd
    ((continuous_exp.tendsto _).comp hf.hasSum) fun _ ↦ prod_one_add_le_exp_sum _ hf₀

end Real
