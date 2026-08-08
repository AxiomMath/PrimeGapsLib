/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.Retained
public import PrimeGapsTheory.Gap246.Variational.Marginal

/-!
# Enlarged-support transfer

Transfer from ε-enlarged permissible support to an auxiliary sieve support with the same
truncation exponent.
-/

@[expose] public section

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY
open scoped PrimeGaps
