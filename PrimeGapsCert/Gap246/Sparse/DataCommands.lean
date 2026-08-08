/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Emit.Commands
public meta import PrimeGapsCert.Gap246.Emit.Commands
public meta import PrimeGapsCert.Gap246.Kernel.LHSScalar
public meta import PrimeGapsCert.Gap246.Kernel.RHS

import PrimeGapsCert.Gap246.Kernel.LHSScalar

/-! # Raw data emission for the packed sparse quadratic forms -/

@[expose] public section

namespace cert246Data.SparseEmit

open Lean
open cert246Data.Emit

/-- Number of source labels combined into one RHS weight checkpoint block. -/
meta def sourceWeightBlockSize : ℕ := 32

/-- Number of stored features combined into one RHS weight checkpoint block. -/
meta def expectedWeightBlockSize : ℕ := 64

/-- Raw type of one LHS scalar-table row check. -/
meta def lhsScalarRowType (dims : SparseGen.LhsDims) (d : ℕ) : Expr :=
  let scalarGeometry := leafTreeLiterals dims.scalarWidth
  eqBool (mkAppN (mkConst ``cert246Data.lhsScalarRowCheck)
    (#[mkNatLit dims.dimension, mkNatLit dims.epsilonDenominator,
        mkNatLit dims.degreeBound, mkNatLit dims.scalarDimension] ++
      #[scalarGeometry[0]!, scalarGeometry[1]!, scalarGeometry[2]!,
        tableExpr realNamespace "lhsScalarMask", tableExpr realNamespace "lhsScalarT",
        mkNatLit d]))
    (mkConst ``Bool.true)

/-- Emit the scalar-table checks outside the hot LHS data dependency. -/
elab "cert246Data_emit_lhs_scalar_checks" : command =>
  Elab.Command.liftCoreM do
    let dims ← readLhsDims
    for d in [0:dims.scalarDimension] do
      addBoolThm (realNamespace ++ Name.mkSimple s!"lhs_scalar_{d}") (lhsScalarRowType dims d)

attribute [nolint defsWithUnderscore] commandCert246Data_emit_lhs_scalar_checks

end cert246Data.SparseEmit
