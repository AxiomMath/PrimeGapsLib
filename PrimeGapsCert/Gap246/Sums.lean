/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Range sums with an offset index

The scan-soundness proofs of the certificate all peel one term off a range sum whose
index is offset by a running cursor. `sum_range_head` is that step, stated once for an
arbitrary additive commutative monoid.
-/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Peel the first term off a range sum whose index is offset by a cursor.

This is `Finset.sum_range_succ'` reindexed so the peeled term keeps the running-cursor shape. -/
theorem sum_range_head {M : Type*} [AddCommMonoid M] (value : ℕ → M) (cursor count : ℕ) :
    ∑ offset ∈ Finset.range (count + 1), value (cursor + offset) =
      value cursor + ∑ offset ∈ Finset.range count, value (cursor + 1 + offset) := by
  rw [Finset.sum_range_succ', Nat.add_zero, add_comm]
  exact congrArg _ (Finset.sum_congr rfl fun offset _ ↦ by
    rw [Nat.add_assoc, Nat.add_comm 1 offset])

end PrimeGaps.Gap246
