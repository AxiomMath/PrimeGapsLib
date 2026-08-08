/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.DataCommands
public meta import PrimeGapsCert.Gap246.Sparse.DataCommands

import PrimeGapsCert.Gap246.Kernel.RHS

/-! # Raw theorem emission for the packed sparse RHS -/

@[expose] public section

namespace cert246Data.SparseEmit

open Lean
open cert246Data.Emit

/-- Raw type of one consecutive sparse RHS-transform check. -/
meta def rhsTransformType (moments : Gen.Dims) (dims : SparseGen.RhsDims)
    (lower upper : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.rhsTransformCheck)
    (leafTreeLiterals dims.transformWidth ++
      #[tableExpr realNamespace "rhsFeatureEnc", tableExpr realNamespace "rhsGroupEnc",
        tableExpr realNamespace "rhsKeyEnc"] ++
      leafTreeLiterals dims.weightWidth ++ leafTreeLiterals moments.pairWidth ++
      #[mkNatLit (2 ^ moments.outputWidth - 1),
        tableExpr realNamespace "rhsTransformT", tableExpr realNamespace "rhsWeightT",
        tableExpr realNamespace "pairT", mkNatLit lower, mkNatLit upper]))
    (mkConst ``Bool.true)

/-- Raw type of one consecutive final RHS-row check. -/
meta def rhsRowType (dims : SparseGen.RhsDims) (lower upper : ℕ) : Expr :=
  let locationGeometry := leafTreeLiterals Gen.indexWidth
  eqBool (mkAppN (mkConst ``cert246Data.rhsRowCheck)
    (#[mkNatLit dims.dimension, mkNatLit dims.groupCount, mkNatLit dims.signatureCount,
        mkNatLit dims.radialDimension, tableExpr realNamespace "rhsFeatureEnc",
        tableExpr realNamespace "rhsGroupEnc", locationGeometry[0]!, locationGeometry[1]!] ++
      leafTreeLiterals dims.transformWidth ++ leafTreeLiterals dims.rowWidth ++
      leafTreeLiterals dims.weightWidth ++ leafTreeLiterals dims.radialWidth ++
      #[tableExpr realNamespace "rhsLocationT", tableExpr realNamespace "rhsTransformT",
        tableExpr realNamespace "rhsRowT", tableExpr realNamespace "rhsWeightT",
        tableExpr realNamespace "rhsRadialT", mkNatLit lower, mkNatLit upper]))
    (mkConst ``Bool.true)

/-- Raw type of one consecutive packed-key range check. -/
meta def rhsKeysRangeType (dims : SparseGen.RhsDims) (lower upper : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.rhsKeysRangeCheck)
    #[mkNatLit dims.groupCount, mkNatLit dims.signatureCount,
      tableExpr realNamespace "rhsKeyEnc", mkNatLit lower, mkNatLit upper])
    (mkConst ``Bool.true)

/-- Raw type of one consecutive feature-signature bound check. -/
meta def rhsFeatureSignatureRangeType (dims : SparseGen.RhsDims) (lower upper : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.rhsFeatureSignatureRangeCheck)
    #[mkNatLit dims.signatureCount, tableExpr realNamespace "rhsFeatureEnc",
      mkNatLit lower, mkNatLit upper])
    (mkConst ``Bool.true)

/-- Raw type of one consecutive location-index group range check. -/
meta def rhsLocationRangeType (dims : SparseGen.RhsDims) (lower upper : ℕ) : Expr :=
  let geometry := leafTreeLiterals Gen.indexWidth
  eqBool (mkAppN (mkConst ``cert246Data.rhsLocationIndexRangeCheck)
    #[mkNatLit dims.signatureCount, mkNatLit dims.transformCount, geometry[0]!, geometry[1]!,
      tableExpr realNamespace "rhsKeyEnc", tableExpr realNamespace "rhsLocationT",
      mkNatLit lower, mkNatLit upper])
    (mkConst ``Bool.true)

/-- Raw type of one consecutive range of RHS marginal-feature key checks. -/
meta def rhsFeatureKeysType (shared : Gen.SharedDims) (dims : SparseGen.RhsDims)
    (lower upper : ℕ) : Expr :=
  let geometry := treeLiterals Gen.indexWidth
  eqBool (mkAppN (mkConst ``cert246Data.rhsFeatureKeysCheck)
    (#[mkNatLit dims.featureCount, mkNatLit shared.degreeBound,
        geometry[0]!, geometry[1]!, geometry[0]!, geometry[1]!,
        tableExpr realNamespace "sigEnc", tableExpr realNamespace "labelEnc",
        tableExpr realNamespace "rhsFeatureEnc", mkNatLit lower, mkNatLit upper,
        tableExpr realNamespace "rhsSourceLocationT",
        tableExpr realNamespace "eraseTargetT"]))
    (mkConst ``Bool.true)

/-- Raw type of one consecutive range of RHS radial-factor recurrence checks. -/
meta def rhsRadialType (shared : Gen.SharedDims) (dims : SparseGen.RhsDims)
    (lower upper : ℕ) : Expr :=
  let geometry := leafTreeLiterals dims.radialWidth
  eqBool (mkAppN (mkConst ``cert246Data.rhsRadialCheck)
    (#[mkNatLit shared.dimension, mkNatLit shared.epsilonDenominator,
        mkNatLit dims.radialDimension, geometry[0]!, geometry[1]!,
        geometry[2]!, geometry[3]!, mkNatLit lower, mkNatLit upper,
        tableExpr realNamespace "rhsRadialT"]))
    (mkConst ``Bool.true)

/-- Raw type of one independently checkable source-label weight block. -/
meta def rhsSourceWeightCheckpointType (shared : Gen.SharedDims) (blockSize block : ℕ) : Expr :=
  let sourceGeometry := treeLiterals Gen.indexWidth
  let coefficientGeometry := leafTreeLiterals shared.coefficientWidth
  eqBool (mkAppN (mkConst ``cert246Data.rhsSourceWeightCheckpointBlockCheck)
    (#[mkNatLit shared.labelCount, mkNatLit shared.degreeBound, sourceGeometry[0]!,
        sourceGeometry[1]!, coefficientGeometry[0]!, coefficientGeometry[1]!,
        coefficientGeometry[2]!, coefficientGeometry[3]!,
        tableExpr realNamespace "rhsWeightLaneWidth", tableExpr realNamespace "sigEnc",
        tableExpr realNamespace "labelEnc", mkNatLit blockSize, mkNatLit block,
        tableExpr realNamespace "rhsSourceLocationT", tableExpr realNamespace "coeffMag",
        tableExpr realNamespace "rhsSourceWeightBoundCheckpoint",
        tableExpr realNamespace "rhsSourceWeightPositiveCheckpoint",
        tableExpr realNamespace "rhsSourceWeightNegativeCheckpoint"]))
    (mkConst ``Bool.true)

/-- Raw type of one independently checkable stored-feature weight block. -/
meta def rhsExpectedWeightCheckpointType (dims : SparseGen.RhsDims)
    (blockSize block : ℕ) : Expr :=
  let weightGeometry := leafTreeLiterals dims.weightWidth
  eqBool (mkAppN (mkConst ``cert246Data.rhsExpectedWeightCheckpointBlockCheck)
    (#[mkNatLit dims.featureCount, weightGeometry[0]!, weightGeometry[1]!,
        weightGeometry[2]!, weightGeometry[3]!, tableExpr realNamespace "rhsWeightLaneWidth",
        mkNatLit blockSize, mkNatLit block, tableExpr realNamespace "rhsWeightT",
        tableExpr realNamespace "rhsExpectedWeightBoundCheckpoint",
        tableExpr realNamespace "rhsExpectedWeightPositiveCheckpoint",
        tableExpr realNamespace "rhsExpectedWeightNegativeCheckpoint"]))
    (mkConst ``Bool.true)

/-- Raw type of the final balance check over the verified weight checkpoints. -/
meta def rhsWeightCheckpointBalanceType (shared : Gen.SharedDims) (dims : SparseGen.RhsDims)
    (sourceBlockSize expectedBlockSize : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.rhsWeightCheckpointBalanceCheck)
    #[tableExpr realNamespace "rhsWeightLaneWidth", mkNatLit (shared.labelCount / sourceBlockSize),
      mkNatLit (dims.featureCount / expectedBlockSize),
      tableExpr realNamespace "rhsSourceWeightBoundCheckpoint",
      tableExpr realNamespace "rhsSourceWeightPositiveCheckpoint",
      tableExpr realNamespace "rhsSourceWeightNegativeCheckpoint",
      tableExpr realNamespace "rhsExpectedWeightBoundCheckpoint",
      tableExpr realNamespace "rhsExpectedWeightPositiveCheckpoint",
      tableExpr realNamespace "rhsExpectedWeightNegativeCheckpoint"])
    (mkConst ``Bool.true)

/-- Number of sparse RHS-transform entries checked by one raw theorem. -/
meta def rhsTransformBlockSize : ℕ := 32

/-- Emit the bounded packed-key and location-index checks. -/
elab "cert246Data_check_rhs_index" : command =>
  Elab.Command.liftCoreM do
    let dims ← readRhsDims
    let keyBlockSize := 256
    let keyBlockCount := (dims.transformCount + keyBlockSize - 1) / keyBlockSize
    for block in [0:keyBlockCount] do
      let lower := block * keyBlockSize
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsKeysBlockCorrect ++ Name.mkSimple s!"case_{block}")
        (rhsKeysRangeType dims lower (min dims.transformCount (lower + keyBlockSize)))
    let locationBlockSize := 8
    let locationBlockCount := (dims.groupCount + locationBlockSize - 1) / locationBlockSize
    for block in [0:locationBlockCount] do
      let lower := block * locationBlockSize
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsLocationBlockCorrect ++ Name.mkSimple s!"case_{block}")
        (rhsLocationRangeType dims lower (min dims.groupCount (lower + locationBlockSize)))
    let featureBlockSize := 256
    let featureBlockCount := (dims.featureCount + featureBlockSize - 1) / featureBlockSize
    for block in [0:featureBlockCount] do
      let lower := block * featureBlockSize
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsFeatureSignatureBlockCorrect ++
          Name.mkSimple s!"case_{block}")
        (rhsFeatureSignatureRangeType dims lower
          (min dims.featureCount (lower + featureBlockSize)))

/-- Number of source labels checked by one raw feature-key theorem. -/
meta def rhsFeatureKeyBlockSize : ℕ := 32

/-- Number of flattened radial entries checked by one raw theorem. -/
meta def rhsRadialBlockSize : ℕ := 128

/-- Emit one balanced slice of the source-label checkpoint comparisons. -/
elab "cert246Data_check_rhs_source_weight_slice" slice:num slices:num : command =>
  Elab.Command.liftCoreM do
    let shared ← readSharedDims
    let slice := slice.getNat
    let slices := slices.getNat
    unless slice < slices do
      throwError "cert246Data: source-weight slice index must lie below the slice count"
    let blockCount := shared.labelCount / sourceWeightBlockSize + 1
    let (first, past) := sliceRange blockCount slices slice
    for block in [first:past] do
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsSourceWeightBlockCorrect ++
          Name.mkSimple s!"case_{block}")
        (rhsSourceWeightCheckpointType shared sourceWeightBlockSize block)

/-- Emit one balanced slice of the stored-feature checkpoint comparisons. -/
elab "cert246Data_check_rhs_expected_weight_slice" slice:num slices:num : command =>
  Elab.Command.liftCoreM do
    let dims ← readRhsDims
    let slice := slice.getNat
    let slices := slices.getNat
    unless slice < slices do
      throwError "cert246Data: expected-weight slice index must lie below the slice count"
    let blockCount := dims.featureCount / expectedWeightBlockSize + 1
    let (first, past) := sliceRange blockCount slices slice
    for block in [first:past] do
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsExpectedWeightBlockCorrect ++
          Name.mkSimple s!"case_{block}")
        (rhsExpectedWeightCheckpointType dims expectedWeightBlockSize block)

/-- Emit the small final balance check over all RHS weight checkpoints. -/
elab "cert246Data_check_rhs_weight_checkpoint_balance" : command =>
  Elab.Command.liftCoreM do
    let shared ← readSharedDims
    let dims ← readRhsDims
    addBoolThm (realNamespace ++ `rhs_weight_checkpoint_balance_ok)
      (rhsWeightCheckpointBalanceType shared dims sourceWeightBlockSize
        expectedWeightBlockSize)

/-- Emit one balanced slice of the RHS transform, row, key, and radial blocks. -/
elab "cert246Data_check_rhs_slice" slice:num slices:num : command =>
  Elab.Command.liftCoreM do
    let shared ← readSharedDims
    let moments ← readDims
    let dims ← readRhsDims
    let slice := slice.getNat
    let slices := slices.getNat
    unless slice < slices do
      throwError "cert246Data: RHS slice index must lie below the slice count"
    let transformCount := (dims.transformCount + rhsTransformBlockSize - 1) /
      rhsTransformBlockSize
    let keyCount := (shared.labelCount + rhsFeatureKeyBlockSize - 1) /
      rhsFeatureKeyBlockSize
    let radialLower := (shared.dimension - 1) * dims.radialDimension
    let radialUpper := dims.radialDimension * dims.radialDimension
    let radialCount := (radialUpper - radialLower + rhsRadialBlockSize - 1) /
      rhsRadialBlockSize
    let (transformLo, transformHi) := sliceRange transformCount slices slice
    let (rowLo, rowHi) := sliceRange dims.groupCount slices slice
    let (keyLo, keyHi) := sliceRange keyCount slices slice
    let (radialLo, radialHi) := sliceRange radialCount slices slice
    for block in [transformLo:transformHi] do
      let lower := block * rhsTransformBlockSize
      let upper := min dims.transformCount (lower + rhsTransformBlockSize)
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsTransformBlockCorrect ++
          Name.mkSimple s!"case_{block}")
        (rhsTransformType moments dims lower upper)
    for row in [rowLo:rowHi] do
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsRowCorrect ++ Name.mkSimple s!"case_{row}")
        (rhsRowType dims row (row + 1))
    for block in [keyLo:keyHi] do
      let lower := block * rhsFeatureKeyBlockSize
      let upper := min shared.labelCount (lower + rhsFeatureKeyBlockSize)
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsFeatureKeyBlockCorrect ++
          Name.mkSimple s!"case_{block}")
        (rhsFeatureKeysType shared dims lower upper)
    for block in [radialLo:radialHi] do
      let lower := radialLower + block * rhsRadialBlockSize
      let upper := min radialUpper (lower + rhsRadialBlockSize)
      addBoolThm
        (`PrimeGaps.Gap246.CertRhsRadialBlockCorrect ++
          Name.mkSimple s!"case_{block}")
        (rhsRadialType shared dims lower upper)

attribute [nolint defsWithUnderscore]
  commandCert246Data_check_rhs_index commandCert246Data_check_rhs_weight_checkpoint_balance

end cert246Data.SparseEmit
