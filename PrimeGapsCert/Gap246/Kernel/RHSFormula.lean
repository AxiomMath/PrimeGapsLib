/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic
public import PrimeGapsCert.Gap246.Kernel.RHS

/-! # Mathematical radial formula for the packed RHS soundness proof -/

@[expose] public section

open scoped Nat

namespace cert246Data

/-- Direct cleared radial factor with all mathematical parameters explicit. -/
noncomputable def rhsRadialFormula (dimension epsilonDenominator q e : ℕ) : ℕ :=
  epsilonDenominator ^ (2 * dimension + 1 - (q + e)) *
    (epsilonDenominator - 1) ^ q *
      ∑ m ∈ Finset.range (e + 1),
        e.choose m * 2 ^ (e - m) * (epsilonDenominator - 1) ^ m * m ! *
          Nat.descFactorial (2 * dimension + 1) (2 * dimension + 1 - (m + q))

end cert246Data
