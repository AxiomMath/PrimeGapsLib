/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# A finite union bound

* `Finset.sum_biUnion_le`: The weighted sum over a finite union is bounded by the sum of the
  individual weighted sums.
-/

@[expose] public section
open Finset

namespace Finset

/-- For a non-negative function `f` into an ordered additive commutative monoid, the sum of `f`
over the finite union is at most the sum over the `A_x` of the sums of `f` over each `A_x`. -/
theorem sum_biUnion_le {ι U N : Type*} [DecidableEq U] [AddCommMonoid N] [Preorder N]
    [AddLeftMono N] (X : Finset ι) (A : ι → Finset U) (f : U → N) (hf : ∀ y, 0 ≤ f y) :
    ∑ y ∈ X.biUnion A, f y ≤ ∑ x ∈ X, ∑ y ∈ A x, f y := by
  have key : ∑ x ∈ X, ∑ y ∈ A x, f y =
      ∑ x ∈ X, ∑ y ∈ X.biUnion A, (if y ∈ A x then f y else 0) :=
    sum_congr rfl fun x hx ↦ by
      rw [sum_ite_mem, inter_eq_right.mpr (subset_biUnion_of_mem A hx)]
  rw [key, sum_comm]
  refine sum_le_sum fun y hy ↦ ?_
  obtain ⟨x, hxX, hxA⟩ := mem_biUnion.1 hy
  have hnn : ∀ x ∈ X, 0 ≤ (if y ∈ A x then f y else 0) :=
    fun x _ ↦ by split; exacts [hf y, le_rfl]
  exact (if_pos hxA).symm.trans_le (single_le_sum hnn hxX)

end Finset
