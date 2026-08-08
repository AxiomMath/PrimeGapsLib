/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Emit.Commands
public meta import PrimeGapsCert.Gap246.Emit.Commands
public meta import PrimeGapsCert.Gap246.Kernel.LHS

import PrimeGapsCert.Gap246.Kernel.LHS

/-! # Raw theorem emission for the packed sparse LHS -/

@[expose] public section

namespace cert246Data.SparseEmit

open Lean
open cert246Data.Emit

/-- Raw type of one consecutive sparse-transform check. -/
meta def lhsTransformType (shared : Gen.SharedDims) (moments : Gen.Dims)
    (dims : SparseGen.LhsDims) (lower upper : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.lhsTransformCheck)
    (leafTreeLiterals dims.transformWidth ++
      #[tableExpr realNamespace "lhsMemberEnc", tableExpr realNamespace "labelEnc",
        tableExpr realNamespace "lhsGroupEnc", tableExpr realNamespace "lhsKeyEnc"] ++
      leafTreeLiterals shared.coefficientWidth ++ leafTreeLiterals moments.pairWidth ++
      #[mkNatLit moments.outputWidth,
        tableExpr realNamespace "lhsTransformT", tableExpr realNamespace "coeffMag",
        tableExpr realNamespace "pairT", mkNatLit lower, mkNatLit upper]))
    (mkConst ``Bool.true)

/-- Raw type of one consecutive final-row check. -/
meta def lhsRowType (shared : Gen.SharedDims) (dims : SparseGen.LhsDims)
    (lower upper : ℕ) : Expr :=
  let locationGeometry := leafTreeLiterals Gen.indexWidth
  let scalarGeometry := leafTreeLiterals dims.scalarWidth
  eqBool (mkAppN (mkConst ``cert246Data.lhsRowCheck)
    (#[mkNatLit dims.groupCount, mkNatLit dims.signatureCount,
        mkNatLit dims.scalarDimension, tableExpr realNamespace "lhsMemberEnc",
        tableExpr realNamespace "labelEnc", tableExpr realNamespace "lhsGroupEnc",
        locationGeometry[0]!, locationGeometry[1]!] ++
      leafTreeLiterals dims.transformWidth ++ leafTreeLiterals dims.rowWidth ++
      leafTreeLiterals shared.coefficientWidth ++
      #[scalarGeometry[0]!, scalarGeometry[1]!, scalarGeometry[2]!,
        tableExpr realNamespace "lhsScalarMask"] ++
      #[tableExpr realNamespace "lhsLocationT", tableExpr realNamespace "lhsTransformT",
        tableExpr realNamespace "lhsRowT", tableExpr realNamespace "coeffMag",
        tableExpr realNamespace "lhsScalarT", mkNatLit lower, mkNatLit upper]))
    (mkConst ``Bool.true)

/-- Raw type of one consecutive packed-key range check. -/
meta def lhsKeysRangeType (dims : SparseGen.LhsDims) (lower upper : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.lhsKeysRangeCheck)
    #[mkNatLit dims.groupCount, mkNatLit dims.signatureCount,
      tableExpr realNamespace "lhsKeyEnc", mkNatLit lower, mkNatLit upper])
    (mkConst ``Bool.true)

/-- Raw type of one consecutive location-index group range check. -/
meta def lhsLocationRangeType (dims : SparseGen.LhsDims) (lower upper : ℕ) : Expr :=
  let geometry := leafTreeLiterals Gen.indexWidth
  eqBool (mkAppN (mkConst ``cert246Data.lhsLocationIndexRangeCheck)
    #[mkNatLit dims.signatureCount, mkNatLit dims.transformCount, geometry[0]!, geometry[1]!,
      tableExpr realNamespace "lhsKeyEnc", tableExpr realNamespace "lhsLocationT",
      mkNatLit lower, mkNatLit upper])
    (mkConst ``Bool.true)

/-- Number of sparse-transform entries checked by one raw theorem. -/
meta def lhsTransformBlockSize : ℕ := 32

/-- Emit the bounded packed-key and location-index checks. -/
elab "cert246Data_check_lhs_index" : command =>
  Elab.Command.liftCoreM do
    let dims ← readLhsDims
    let keyBlockSize := 256
    let keyBlockCount := (dims.transformCount + keyBlockSize - 1) / keyBlockSize
    for block in [0:keyBlockCount] do
      let lower := block * keyBlockSize
      addBoolThm
        (`PrimeGaps.Gap246.CertLhsKeysBlockCorrect ++ Name.mkSimple s!"case_{block}")
        (lhsKeysRangeType dims lower (min dims.transformCount (lower + keyBlockSize)))
    let locationBlockSize := 8
    let locationBlockCount := (dims.groupCount + locationBlockSize - 1) / locationBlockSize
    for block in [0:locationBlockCount] do
      let lower := block * locationBlockSize
      addBoolThm
        (`PrimeGaps.Gap246.CertLhsLocationBlockCorrect ++ Name.mkSimple s!"case_{block}")
        (lhsLocationRangeType dims lower (min dims.groupCount (lower + locationBlockSize)))

/-- Emit one balanced slice of the full-certificate LHS transform blocks and rows. -/
elab "cert246Data_check_lhs_slice" slice:num slices:num : command =>
  Elab.Command.liftCoreM do
    let shared ← readSharedDims
    let moments ← readDims
    let dims ← readLhsDims
    let slice := slice.getNat
    let slices := slices.getNat
    unless slice < slices do
      throwError "cert246Data: LHS slice index must lie below the slice count"
    let blockCount := (dims.transformCount + lhsTransformBlockSize - 1) /
      lhsTransformBlockSize
    let (blockLo, blockHi) := sliceRange blockCount slices slice
    let (rowLo, rowHi) := sliceRange dims.groupCount slices slice
    for block in [blockLo:blockHi] do
      let lower := block * lhsTransformBlockSize
      let upper := min dims.transformCount (lower + lhsTransformBlockSize)
      addBoolThm
        (`PrimeGaps.Gap246.CertLhsTransformBlockCorrect ++
          Name.mkSimple s!"case_{block}")
        (lhsTransformType shared moments dims lower upper)
    for row in [rowLo:rowHi] do
      addBoolThm
        (`PrimeGaps.Gap246.CertLhsRowCorrect ++ Name.mkSimple s!"case_{row}")
        (lhsRowType shared dims row (row + 1))

attribute [nolint defsWithUnderscore] commandCert246Data_check_lhs_index

end cert246Data.SparseEmit
