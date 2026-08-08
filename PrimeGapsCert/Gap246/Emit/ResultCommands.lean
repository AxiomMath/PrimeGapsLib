/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Emit.LevelCommands
public meta import PrimeGapsCert.Gap246.Emit.LevelCommands
public meta import PrimeGapsCert.Gap246.Kernel.MomentBound

import PrimeGapsCert.Gap246.Kernel.MomentBound

/-! # Theorem emission for reconstructed packed moment results -/

@[expose] public section

namespace cert246Data.Emit

open Lean

/-- Raw type of one final reconstruction block over the uniform-width ladder. -/
meta def resultType (ns : Name) (dims : Gen.Dims) (lo hi index : ℕ) : Expr :=
  let triangular := dims.signatureCount * (dims.signatureCount + 1) / 2
  eqBool (mkAppN (mkConst ``cert246Data.nilResultCheck)
    (#[mkNatLit triangular] ++ treeLiterals dims.nilWidth ++
      #[mkNatLit dims.outputWidth] ++ leafTreeLiterals dims.pairWidth ++
      #[mkNatLit dims.dimension, mkNatLit dims.maxLevel, tableExpr ns "sigEnc",
        tableExpr ns "nilT", tableExpr ns "pairT",
        mkNatLit lo, mkNatLit hi, mkNatLit index]))
    (mkConst ``Bool.true)

/-- Raw type of one fused result-and-bound block over independent levels. -/
meta def levelResultBoundType (ns : Name) (dims : Gen.Dims) (lo hi index : ℕ) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.nilResultBoundLevelsCheck)
    (#[mkNatLit dims.outputWidth] ++ leafTreeLiterals dims.pairWidth ++
      #[tableExpr ns "coeffT", mkNatLit dims.maxLevel, tableExpr ns "sigEnc"] ++
      levelDataExprs ns ++ #[tableExpr ns "pairT", mkNatLit lo, mkNatLit hi,
        mkNatLit index]))
    (mkConst ``Bool.true)

/-- Raw type of the packed binomial-coefficient table check. -/
meta def coefficientType (ns : Name) (dims : Gen.Dims) : Expr :=
  eqBool (mkAppN (mkConst ``cert246Data.coeffCheck)
    #[mkNatLit dims.dimension, mkNatLit dims.maxLevel, tableExpr ns "coeffT"])
    (mkConst ``Bool.true)

/-- Emit every row block of the final uniform-width binomial reconstruction. -/
elab "cert246Data_check_moment_result" : command =>
  Elab.Command.liftCoreM do
    let dims ← readDims
    let blocks := rowBlocks dims.signatureCount blockEntries
    for block in [0:blocks.size] do
      let (lo, hi, index) := blocks[block]!
      addBoolThm (realNamespace ++ Name.mkSimple s!"nil_result_{block}")
        (resultType realNamespace dims lo hi index)

/-- Check the packed binomial coefficients of the split-level reconstruction. -/
elab "cert246Data_check_coefficients" : command =>
  Elab.Command.liftCoreM do
    addBoolThm (realNamespace ++ `coeff_ok) (coefficientType realNamespace (← readDims))

/-- Emit every fused split-level final-result and predecessor-bound block. -/
elab "cert246Data_check_moment_result_bound_split" : command =>
  Elab.Command.liftCoreM do
    let dims ← readDims
    let blocks := rowBlocks dims.signatureCount blockEntries
    for block in [0:blocks.size] do
      let (lo, hi, index) := blocks[block]!
      addBoolThm (realNamespace ++ Name.mkSimple s!"nil_level_result_bound_{block}")
        (levelResultBoundType realNamespace dims lo hi index)

/-- Emit one round-robin worker's share of the fused split-level result blocks. -/
elab "cert246Data_check_moment_result_bound_split_worker" worker:num workers:num : command =>
  Elab.Command.liftCoreM do
    let workerIndex := worker.getNat
    let workerCount := workers.getNat
    unless 0 < workerCount && workerIndex < workerCount do
      throwError "cert246Data: result worker must lie in 0..worker-count-1"
    let dims ← readDims
    let blocks := rowBlocks dims.signatureCount blockEntries
    for block in [0:blocks.size] do
      if block % workerCount = workerIndex then
        let (lo, hi, index) := blocks[block]!
        addBoolThm (realNamespace ++ Name.mkSimple s!"nil_level_result_bound_{block}")
          (levelResultBoundType realNamespace dims lo hi index)

attribute [nolint defsWithUnderscore]
  commandCert246Data_check_moment_result commandCert246Data_check_moment_result_bound_split
  commandCert246Data_check_coefficients

end cert246Data.Emit
