/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Finsupp.Basic


/-! # Basic properties of Finsupp -/

@[expose] public section

namespace Finsupp
variable {α M : Type*} [Zero M] {f : α →₀ M}

@[simp] theorem nonempty_frange_iff : f.frange.Nonempty ↔ f ≠ 0 := by
  simp [Finset.Nonempty, Finsupp.ext_iff]

end Finsupp
