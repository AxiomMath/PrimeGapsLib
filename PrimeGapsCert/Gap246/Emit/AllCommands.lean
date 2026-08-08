/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Emit.LevelDataCommands
public meta import PrimeGapsCert.Gap246.Emit.LevelDataCommands
public import PrimeGapsCert.Gap246.Sparse.DataCommands
public meta import PrimeGapsCert.Gap246.Sparse.DataCommands

/-! # Modular emission of generated certificate data

Each stage consumes the packed declarations emitted by its predecessor.  Thus separate Lean
modules can own the shared, moment, LHS, and RHS data without rerunning an earlier generator.
-/

@[expose] public section

namespace cert246Data.Emit

open Lean
open cert246Data.SparseEmit

/-- Rebuild the host value consumed by the LHS and RHS generators from the recorded store. -/
meta def readGeneratedBase : CoreM SourceGen.Base := do
  let (dims, input) ← readShared
  let (_, top, predecessor) ← readMoments
  return { dims, input, top, predecessor }

/-- Read the JSON once, record the derived input, and emit the shared packed data. -/
elab "cert246Data_emit_generated_shared" : command =>
  Elab.Command.liftCoreM do
    let raw ← SourceGen.readRaw (← readThe Core.Context).fileName
    let input ← IO.ofExcept (SourceGen.sharedInput raw)
    let tables := Gen.generateShared SourceGen.epsilonDenominator input
    recordDerived (.shared tables.dims input)
    addNatAbbrev (realNamespace ++ `sigEnc) tables.sigEnc
    addNatDef (realNamespace ++ `eraseEnc) tables.eraseEnc
    addTreeDef (realNamespace ++ `eraseTargetT) tables.eraseTargetLeaves
    addNatAbbrev (realNamespace ++ `labelEnc) tables.labelEnc
    addTreeAbbrev (realNamespace ++ `coeffMag)
      (Gen.regroupLevelLeaves tables.dims.coefficientWidth tables.coefficientLeaves)
    addNatDef (realNamespace ++ `factT) tables.factT

/-- Compute the moment ladder once from the recorded input and record its dimensions. -/
elab "cert246Data_emit_generated_moments" : command =>
  Elab.Command.liftCoreM do
    let (sharedDims, input) ← readShared
    let moments := Gen.generate
      { dimension := sharedDims.dimension, signatures := input.signatures }
    unless moments.levelWidths.size = moments.dims.maxLevel + 1 &&
        moments.levelLeaves.size = moments.dims.maxLevel + 1 do
      throwError "cert246Data: generated moment dimensions disagree"
    recordDerived (.moments moments.dims moments.top moments.predecessor)
    for level in [0:moments.levelLeaves.size] do
      let width := moments.levelWidths[level]!
      let shift := Gen.levelChunkShift width
      addNatAbbrev (levelName "nilLevelShift" level) shift
      addNatAbbrev (levelName "nilLevelPmask" level) ((1 <<< shift) - 1)
      addNatAbbrev (levelName "nilLevelWidth" level) width
      addNatAbbrev (levelName "nilLevelMask" level) ((1 <<< width) - 1)
      addTreeDef (levelName "nilLevelT" level)
        (Gen.regroupLevelLeaves width moments.levelLeaves[level]!)
    let shifts := moments.levelWidths.map Gen.levelChunkShift
    let pmasks := shifts.map fun shift ↦ (1 <<< shift) - 1
    let masks := moments.levelWidths.map fun width ↦ (1 <<< width) - 1
    addTreeAbbrev (realNamespace ++ `nilLevelWidths) moments.levelWidths
    addTreeAbbrev (realNamespace ++ `nilLevelShifts) shifts
    addTreeAbbrev (realNamespace ++ `nilLevelPmasks) pmasks
    addTreeAbbrev (realNamespace ++ `nilLevelMasks) masks
    let references := (Array.range moments.levelLeaves.size).map fun level ↦
      mkConst (levelName "nilLevelT" level)
    addTreeReferenceAbbrev (realNamespace ++ `nilLevelTrees) references
    addTreeDef (realNamespace ++ `pairT)
      (Gen.regroupLevelLeaves moments.dims.pairWidth moments.pairLeaves)
    addNatAbbrev (realNamespace ++ `coeffT)
      (Gen.packTable 128 ((Array.range (moments.dims.maxLevel + 1)).map fun level ↦
        (moments.dims.dimension - 1).choose level +
          (moments.dims.dimension.choose level <<< 64)))

/-- Generate every LHS table from the recorded source and moments. -/
elab "cert246Data_emit_generated_lhs" : command =>
  Elab.Command.liftCoreM do
    let tables := SourceGen.generateLhsTables (← readGeneratedBase)
    recordDerived (.lhs tables.dims)
    addNatDef (realNamespace ++ `lhsGroupEnc) tables.groupEnc
    addNatDef (realNamespace ++ `lhsMemberEnc) tables.memberEnc
    addNatDef (realNamespace ++ `lhsInverseEnc) tables.inverseEnc
    addNatDef (realNamespace ++ `lhsKeyEnc) tables.keyEnc
    addTreeDef (realNamespace ++ `lhsLocationT)
      (Gen.regroupLevelLeaves Gen.indexWidth tables.locationLeaves)
    addTreeDef (realNamespace ++ `lhsTransformT)
      (Gen.regroupLevelLeaves tables.dims.transformWidth tables.transformLeaves)
    addTreeDef (realNamespace ++ `lhsRowT)
      (Gen.regroupLevelLeaves tables.dims.rowWidth tables.rowLeaves)
    addTreeDef (realNamespace ++ `lhsScalarT)
      (Gen.regroupLevelLeaves tables.dims.scalarWidth tables.scalarLeaves)
    addNatDef (realNamespace ++ `lhsScalarMask) (2 ^ tables.dims.scalarWidth - 1)
    unless tables.dims.groupCount > 0 do
      throwError "cert246Data: empty LHS group family"

/-- Generate every RHS table and checkpoint from the recorded source and moments. -/
elab "cert246Data_emit_generated_rhs" : command =>
  Elab.Command.liftCoreM do
    let base ← readGeneratedBase
    let source := SourceGen.generateRhsSource base
    let tables := SparseGen.generateRhs base.dims base.input source.features
      source.groups source.keys source.transforms source.rows
    recordDerived (.rhs tables.dims)
    addNatDef (realNamespace ++ `rhsFeatureEnc) tables.featureEnc
    addNatDef (realNamespace ++ `rhsGroupEnc) tables.groupEnc
    addNatDef (realNamespace ++ `rhsInverseEnc) tables.inverseEnc
    addNatDef (realNamespace ++ `rhsKeyEnc) tables.keyEnc
    addTreeAbbrev (realNamespace ++ `rhsSourceLocationT) tables.sourceLocationLeaves
    addTreeAbbrev (realNamespace ++ `rhsWeightT)
      (Gen.regroupLevelLeaves tables.dims.weightWidth tables.weightLeaves)
    addTreeDef (realNamespace ++ `rhsLocationT)
      (Gen.regroupLevelLeaves Gen.indexWidth tables.locationLeaves)
    addTreeDef (realNamespace ++ `rhsTransformT)
      (Gen.regroupLevelLeaves tables.dims.transformWidth tables.transformLeaves)
    addTreeDef (realNamespace ++ `rhsRowT)
      (Gen.regroupLevelLeaves tables.dims.rowWidth tables.rowLeaves)
    addTreeDef (realNamespace ++ `rhsRadialT)
      (Gen.regroupLevelLeaves tables.dims.radialWidth tables.radialLeaves)
    unless tables.dims.groupCount > 0 do
      throwError "cert246Data: empty RHS group family"
    let checkpoints := SparseGen.generateRhsWeightCheckpoints base.dims base.input
      source.features sourceWeightBlockSize expectedWeightBlockSize
    addNatAbbrev (realNamespace ++ `rhsWeightLaneWidth) checkpoints.laneWidth
    addNatAbbrev (realNamespace ++ `rhsSourceWeightBlockSize) checkpoints.sourceBlockSize
    addTreeDef (realNamespace ++ `rhsSourceWeightBoundCheckpoint) checkpoints.sourceBound
    addTreeDef (realNamespace ++ `rhsSourceWeightPositiveCheckpoint) checkpoints.sourcePositive
    addTreeDef (realNamespace ++ `rhsSourceWeightNegativeCheckpoint) checkpoints.sourceNegative
    addNatAbbrev (realNamespace ++ `rhsExpectedWeightBlockSize) checkpoints.expectedBlockSize
    addTreeDef (realNamespace ++ `rhsExpectedWeightBoundCheckpoint) checkpoints.expectedBound
    addTreeDef (realNamespace ++ `rhsExpectedWeightPositiveCheckpoint) checkpoints.expectedPositive
    addTreeDef (realNamespace ++ `rhsExpectedWeightNegativeCheckpoint) checkpoints.expectedNegative

attribute [nolint defsWithUnderscore]
  commandCert246Data_emit_generated_shared commandCert246Data_emit_generated_moments
  commandCert246Data_emit_generated_lhs commandCert246Data_emit_generated_rhs

end cert246Data.Emit
