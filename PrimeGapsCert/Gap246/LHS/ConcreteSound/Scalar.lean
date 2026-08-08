/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.LHS.ConcreteSound.Contraction
public import PrimeGapsCert.Gap246.LHS.ScalarDefs

import Mathlib.Tactic.IntervalCases

/-! # Concrete soundness for the packed sparse LHS scalar table -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Every stored LHS scalar is its direct enlarged-simplex arithmetic value. -/
theorem certLhsScalar_correct (d aSum : ℕ) (hd : d ≤ 50) (haSum : aSum ≤ d) :
    cert246Data.treeAt 6 63 1024 cert246Data.lhsScalarMask cert246Data.lhsScalarT
        (d * 51 + aSum) = certFactorTables.iScalar d aSum := by
  have hrow : cert246Data.lhsScalarRowCheck 50 25 25 51 6 63 1024
      cert246Data.lhsScalarMask cert246Data.lhsScalarT d = true := by
    interval_cases d
    · exact cert246Data.lhs_scalar_0
    · exact cert246Data.lhs_scalar_1
    · exact cert246Data.lhs_scalar_2
    · exact cert246Data.lhs_scalar_3
    · exact cert246Data.lhs_scalar_4
    · exact cert246Data.lhs_scalar_5
    · exact cert246Data.lhs_scalar_6
    · exact cert246Data.lhs_scalar_7
    · exact cert246Data.lhs_scalar_8
    · exact cert246Data.lhs_scalar_9
    · exact cert246Data.lhs_scalar_10
    · exact cert246Data.lhs_scalar_11
    · exact cert246Data.lhs_scalar_12
    · exact cert246Data.lhs_scalar_13
    · exact cert246Data.lhs_scalar_14
    · exact cert246Data.lhs_scalar_15
    · exact cert246Data.lhs_scalar_16
    · exact cert246Data.lhs_scalar_17
    · exact cert246Data.lhs_scalar_18
    · exact cert246Data.lhs_scalar_19
    · exact cert246Data.lhs_scalar_20
    · exact cert246Data.lhs_scalar_21
    · exact cert246Data.lhs_scalar_22
    · exact cert246Data.lhs_scalar_23
    · exact cert246Data.lhs_scalar_24
    · exact cert246Data.lhs_scalar_25
    · exact cert246Data.lhs_scalar_26
    · exact cert246Data.lhs_scalar_27
    · exact cert246Data.lhs_scalar_28
    · exact cert246Data.lhs_scalar_29
    · exact cert246Data.lhs_scalar_30
    · exact cert246Data.lhs_scalar_31
    · exact cert246Data.lhs_scalar_32
    · exact cert246Data.lhs_scalar_33
    · exact cert246Data.lhs_scalar_34
    · exact cert246Data.lhs_scalar_35
    · exact cert246Data.lhs_scalar_36
    · exact cert246Data.lhs_scalar_37
    · exact cert246Data.lhs_scalar_38
    · exact cert246Data.lhs_scalar_39
    · exact cert246Data.lhs_scalar_40
    · exact cert246Data.lhs_scalar_41
    · exact cert246Data.lhs_scalar_42
    · exact cert246Data.lhs_scalar_43
    · exact cert246Data.lhs_scalar_44
    · exact cert246Data.lhs_scalar_45
    · exact cert246Data.lhs_scalar_46
    · exact cert246Data.lhs_scalar_47
    · exact cert246Data.lhs_scalar_48
    · exact cert246Data.lhs_scalar_49
    · exact cert246Data.lhs_scalar_50
  rw [lhsScalarRowCheck_sound hrow hd aSum (by omega) haSum]
  simp only [cert246Data.lhsScalarFormula, factorialFold_eq_factorial,
    descFactorialFold_eq_descFactorial, Nat.add_eq, Nat.mul_eq, Nat.sub_eq, Nat.pow_eq]
  rfl

end PrimeGaps.Gap246
