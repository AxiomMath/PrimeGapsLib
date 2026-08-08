/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Nat.Factorial.Basic
public import PrimeGapsCert.Gap246.Kernel.LHS

/-! # Auxiliary scalar-table checks for the packed LHS certificate -/

@[expose] public section

namespace cert246Data

/-- Direct enlarged-simplex scalar with every mathematical parameter explicit. -/
noncomputable def lhsScalarFormula
    (dimension epsilonDenominator degreeBound d aSum : ℕ) : ℕ :=
  Nat.mul
    (Nat.mul
      (Nat.mul
        (Nat.mul (Nat.pow (Nat.add epsilonDenominator 1) (Nat.add dimension d))
          (Nat.pow epsilonDenominator (Nat.sub (Nat.add dimension 1) d)))
        (factorialFold aSum))
      (descFactorialFold (Nat.add (Nat.mul 2 dimension) 1)
        (Nat.sub (Nat.add dimension 1) d)))
    (Nat.pow (factorialFold (Nat.add degreeBound 1)) 2)

/-- Check one row of stored enlarged-simplex scalars. -/
noncomputable def lhsScalarRowCheck
    (dimension epsilonDenominator degreeBound scalarDimension scalarCs scalarPmask scalarWidth
      scalarMask : ℕ) (scalarTree : Lean.RArray ℕ) (d : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis aSum ↦
      Bool.rec false (inductionHypothesis aSum.succ)
        (Nat.beq (treeAt scalarCs scalarPmask scalarWidth scalarMask scalarTree
            (Nat.add (Nat.mul d scalarDimension) aSum))
          (Bool.rec 0 (lhsScalarFormula dimension epsilonDenominator degreeBound d aSum)
            (Bool.and' (Nat.ble d dimension) (Nat.ble aSum d)))))
    scalarDimension 0

end cert246Data
