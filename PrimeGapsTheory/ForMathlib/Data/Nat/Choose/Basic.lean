/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Choose.Basic


/-! # Multichoose -/

@[expose] public section

namespace Nat

@[simp] lemma multichoose_eq_zero_iff {r n : ℕ} : r.multichoose n = 0 ↔ r = 0 ∧ n ≠ 0 := by
  rw [multichoose_eq, choose_eq_zero_iff]
  grind

end Nat
