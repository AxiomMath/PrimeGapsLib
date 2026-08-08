/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-! # Bounds on the reciprocal of `1 - x⁻¹` -/

@[expose] public section

/-- For `1 < x`, the reciprocal of `1 - x⁻¹` is at least `1`. -/
theorem one_le_one_sub_inv_inv {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {x : K} (hx : 1 < x) : 1 ≤ (1 - x⁻¹)⁻¹ :=
  (one_le_inv₀ (sub_pos.mpr (inv_lt_one_of_one_lt₀ hx))).mpr <|
    sub_le_self 1 (inv_nonneg.mpr (zero_le_one.trans hx.le))
