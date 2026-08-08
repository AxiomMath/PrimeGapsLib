/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Combinatorics.Enumerative.Composition


/-! # Compositions of a natural number -/

@[expose] public section

open Finset Composition

@[simp] theorem Composition.univ_zero : (univ : Finset (Composition 0)) = {ones 0} := rfl
