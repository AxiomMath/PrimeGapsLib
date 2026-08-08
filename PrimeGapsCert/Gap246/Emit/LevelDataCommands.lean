/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Emit.Commands
public meta import PrimeGapsCert.Gap246.Emit.Commands

/-! # Dependency-isolated nilpotent-level data emission -/

@[expose] public section

namespace cert246Data.Emit

open Lean

/-- Name of one independently cached nilpotent-level object. -/
meta def levelName (stem : String) (level : ℕ) : Name :=
  realNamespace ++ Name.mkSimple s!"{stem}{level}"

end cert246Data.Emit
