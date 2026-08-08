/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic


/-! # Operations on Finsupp -/

@[expose] public section

namespace Finsupp
variable {α M N : Type*} [Zero M] [CommMonoid N] {a : α} {b : M} {h : α → M → N}

@[to_additive]
theorem prod_single_index_of_ne (hb : b ≠ 0) : (single a b).prod h = h a b := by
  simp [prod, hb]

end Finsupp
