/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Emit.Commands
public meta import PrimeGapsCert.Gap246.Emit.Commands

import PrimeGapsCert.Gap246.Kernel.Moments

/-! # Theorem emission for independently packed nilpotent levels -/

@[expose] public section

namespace cert246Data.Emit

open Lean

/-- Cached assignment of every `(level, block)` check to one numerical worker. -/
structure MomentWorkerPlan where
  workerCount : ℕ
  maxLevel : ℕ
  blockCount : ℕ
  sliceCount : ℕ
  assignments : Array ℕ
  slices : Array ℕ
attribute [nolint docBlame] MomentWorkerPlan.workerCount MomentWorkerPlan.maxLevel
  MomentWorkerPlan.blockCount MomentWorkerPlan.sliceCount MomentWorkerPlan.assignments
  MomentWorkerPlan.slices

/-- Workers sharing each nilpotent level's blocks, cut to balance the levels' check cost. -/
meta def levelWorkers : Array (Array ℕ) := #[
  #[], #[4], #[1], #[1, 3], #[5, 4, 6, 5, 3], #[2, 5, 7, 5, 4, 7, 5], #[2, 2, 3, 0, 3, 6, 4, 0],
  #[1, 2, 1, 7, 2, 4, 3, 1], #[7, 6, 6, 3, 1, 2, 6], #[3, 0, 6, 5, 7, 6], #[5, 2, 1, 7],
  #[0, 0, 7], #[4, 4], #[0], #[4], #[0], #[1], #[0], #[0], #[5], #[6], #[5], #[7], #[0], #[7]
]

/-- Deterministically distribute each level's blocks among its assigned workers. -/
meta def readMomentWorkerPlan : CoreM MomentWorkerPlan := do
  let dimensions ← readDims
  unless levelWorkers.size = dimensions.maxLevel + 1 do
    throwError "cert246Data: the worker schedule covers {levelWorkers.size - 1} levels, \
      the certificate has {dimensions.maxLevel}"
  let blockCount := (rowBlocks dimensions.signatureCount blockEntries).size
  let mut assignments := #[]
  let mut slices := #[]
  for level in [1:dimensions.maxLevel + 1] do
    let workers := levelWorkers[level]!
    for block in [0:blockCount] do
      assignments := assignments.push workers[block % workers.size]!
      slices := slices.push (block % 5)
  return {
    workerCount := 8
    maxLevel := dimensions.maxLevel
    blockCount
    sliceCount := 5
    assignments
    slices
  }

/-- Constants describing the independently packed nilpotent levels. -/
meta def levelDataExprs (ns : Name) : Array Expr :=
  #[tableExpr ns "nilLevelShifts", tableExpr ns "nilLevelPmasks",
    tableExpr ns "nilLevelWidths", tableExpr ns "nilLevelMasks",
    tableExpr ns "nilLevelTrees"]

/-- Raw type of one independently packed level-zero block. -/
meta def levelBaseType (ns : Name) (lo hi index : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.nilBaseLevelsCheck)
    (#[tableExpr ns "sigEnc"] ++ levelDataExprs ns ++
      #[mkNatLit lo, mkNatLit hi, mkNatLit index]))
    (mkConst ``Bool.true)

/-- Raw type of one independently packed transition block. -/
meta def levelStepType (ns : Name) (level lo hi index : ℕ) : Expr :=
  let previous := level - 1
  let levelExpr := fun stem requested ↦
    tableExpr ns s!"{stem}{requested}"
  eqBool (mkAppN (mkConst ``cert246Data.nilStepTreesCheck)
    #[levelExpr "nilLevelShift" level, levelExpr "nilLevelPmask" level,
      levelExpr "nilLevelWidth" level, levelExpr "nilLevelMask" level,
      levelExpr "nilLevelShift" previous, levelExpr "nilLevelPmask" previous,
      levelExpr "nilLevelWidth" previous, levelExpr "nilLevelMask" previous,
      tableExpr ns "sigEnc", tableExpr ns "eraseEnc", tableExpr ns "factT", mkNatLit level,
      levelExpr "nilLevelT" level, levelExpr "nilLevelT" previous,
      mkNatLit lo, mkNatLit hi, mkNatLit index])
    (mkConst ``Bool.true)

/-- Emit level-zero checks for the independently packed ladder. -/
elab "cert246Data_check_level_base" : command =>
  Elab.Command.liftCoreM do
    let dims ← readDims
    let blocks := rowBlocks dims.signatureCount blockEntries
    for block in [0:blocks.size] do
      let (lo, hi, index) := blocks[block]!
      addBoolThm (realNamespace ++ Name.mkSimple s!"nil_level_base_{block}")
        (levelBaseType realNamespace lo hi index)

/-- Emit the load-balanced subset of full transition blocks assigned to one worker. -/
elab "cert246Data_check_nil_worker" requested:num : command =>
  Elab.Command.liftCoreM do
    let worker := requested.getNat
    let dimensions ← readDims
    let plan ← readMomentWorkerPlan
    let blocks := rowBlocks dimensions.signatureCount blockEntries
    unless plan.maxLevel = dimensions.maxLevel && plan.blockCount = blocks.size &&
        plan.assignments.size = dimensions.maxLevel * blocks.size do
      throwError "cert246Data: moment-worker plan disagrees with the committed dimensions"
    unless worker < plan.workerCount do
      throwError "cert246Data: moment worker must lie in 0..{plan.workerCount - 1}"
    unless plan.assignments.all (· < plan.workerCount) do
      throwError "cert246Data: moment-worker plan contains an invalid assignment"
    for level in [1:dimensions.maxLevel + 1] do
      for block in [0:blocks.size] do
        if plan.assignments[(level - 1) * blocks.size + block]! = worker then
          let (lo, hi, index) := blocks[block]!
          addBoolThm (realNamespace ++ Name.mkSimple s!"nil_level_step_{level}_{block}")
            (levelStepType realNamespace level lo hi index)

attribute [nolint defsWithUnderscore] commandCert246Data_check_level_base

end cert246Data.Emit
