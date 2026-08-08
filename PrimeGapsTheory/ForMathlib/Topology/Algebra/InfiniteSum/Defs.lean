/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Defs


/-! # Infinite sums -/

@[expose] public section

theorem Summable.of_tsum_ne_zero {α β : Type*} [AddCommMonoid α] [TopologicalSpace α]
    {f : β → α} {L : SummationFilter β} (ih : tsum f L ≠ 0) : Summable f L := by
  grind [tsum_eq_zero_of_not_summable]
