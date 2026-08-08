/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.BoundSound
public import PrimeGapsCert.Gap246.Moments.Gather

/-! # Gathering independently packed nilpotent-level checks -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Rows of a checked independently packed base level. -/
abbrev LevelBaseRange (sigEnc : ℕ) (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (lower upper : ℕ) : Prop :=
  Range
    (fun s t ↦ cert246Data.nilLevelAt shifts pmasks widths masks trees 0
      (cert246Data.triIdx s t))
    (fun s t ↦ if cert246Data.sigField sigEnc s = 0 ∧
      cert246Data.sigField sigEnc t = 0 then 1 else 0) lower upper

/-- One emitted independently packed base block as a mathematical row range. -/
theorem levelBaseBlock {sigEnc : ℕ} {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {lower upper index : ℕ}
    (h : cert246Data.nilBaseLevelsCheck sigEnc shifts pmasks widths masks trees
      lower upper index = true)
    (hgeometry : decide (pmasks.get 0 + 1 = 2 ^ shifts.get 0) = true)
    (hindex : decide (index = lower * (lower + 1) / 2) = true) :
    LevelBaseRange sigEnc shifts pmasks widths masks trees lower upper :=
  rangeBlock (fun hindex' ↦ nilBaseLevelsCheck_sound
    (of_decide_eq_true hgeometry) hindex' h) hindex

/-- Adjacent independently packed base ranges splice. -/
theorem levelBaseSplice {sigEnc : ℕ} {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {lower middle upper : ℕ}
    (left : LevelBaseRange sigEnc shifts pmasks widths masks trees lower middle)
    (right : LevelBaseRange sigEnc shifts pmasks widths masks trees middle upper) :
    LevelBaseRange sigEnc shifts pmasks widths masks trees lower upper :=
  rangeSplice left right

/-- Finish a complete independently packed base range. -/
theorem levelBaseFinish {sigEnc : ℕ} {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {upper : ℕ}
    (h : LevelBaseRange sigEnc shifts pmasks widths masks trees 0 upper) :
    ∀ t < upper, ∀ s ≤ t,
      cert246Data.nilLevelAt shifts pmasks widths masks trees 0
          (cert246Data.triIdx s t) =
        if cert246Data.sigField sigEnc s = 0 ∧
            cert246Data.sigField sigEnc t = 0 then 1 else 0 :=
  rangeFinish h

/-! ## Dependency-isolated two-tree transition ranges -/

/-- Rows of a transition check that imports only its current and preceding packed trees. -/
abbrev TreeLevelStepRange
    (currentShift currentPmask currentWidth currentMask previousShift previousPmask
      previousWidth previousMask sigEnc eraseEnc factT level : ℕ)
    (currentTree previousTree : Lean.RArray ℕ) (lower upper : ℕ) : Prop :=
  Range
    (fun s t ↦
      let active := cert246Data.nilActive level
        (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField sigEnc t))
      Bool.rec (motive := fun _ ↦ ℕ) 0
        (cert246Data.treeAt currentShift currentPmask currentWidth currentMask currentTree
          (cert246Data.triIdx s t)) active)
    (fun s t ↦
      let active := cert246Data.nilActive level
        (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField sigEnc t))
      Bool.rec (motive := fun _ ↦ ℕ) 0
        (cert246Data.nilTreeEntry sigEnc eraseEnc factT level previousShift previousPmask
          previousWidth previousMask previousTree s t) active) lower upper

/-- One emitted dependency-isolated transition block as a mathematical row range. -/
theorem treeLevelStepBlock
    {currentShift currentPmask currentWidth currentMask previousShift previousPmask
      previousWidth previousMask sigEnc eraseEnc factT level : ℕ}
    {currentTree previousTree : Lean.RArray ℕ} {lower upper index : ℕ}
    (h : cert246Data.nilStepTreesCheck currentShift currentPmask currentWidth currentMask
      previousShift previousPmask previousWidth previousMask sigEnc eraseEnc factT level
      currentTree previousTree lower upper index = true)
    (hindex : decide (index = lower * (lower + 1) / 2) = true) :
    TreeLevelStepRange currentShift currentPmask currentWidth currentMask previousShift
      previousPmask previousWidth previousMask sigEnc eraseEnc factT level currentTree
      previousTree lower upper :=
  rangeBlock (fun hindex' ↦ nilStepTreesCheck_sound hindex' h) hindex

/-- Adjacent dependency-isolated transition ranges splice. -/
theorem treeLevelStepSplice
    {currentShift currentPmask currentWidth currentMask previousShift previousPmask
      previousWidth previousMask sigEnc eraseEnc factT level : ℕ}
    {currentTree previousTree : Lean.RArray ℕ} {lower middle upper : ℕ}
    (left : TreeLevelStepRange currentShift currentPmask currentWidth currentMask previousShift
      previousPmask previousWidth previousMask sigEnc eraseEnc factT level currentTree
      previousTree lower middle)
    (right : TreeLevelStepRange currentShift currentPmask currentWidth currentMask previousShift
      previousPmask previousWidth previousMask sigEnc eraseEnc factT level currentTree
      previousTree middle upper) :
    TreeLevelStepRange currentShift currentPmask currentWidth currentMask previousShift
      previousPmask previousWidth previousMask sigEnc eraseEnc factT level currentTree
      previousTree lower upper :=
  rangeSplice left right

/-- Finish a complete dependency-isolated transition range. -/
theorem treeLevelStepFinish
    {currentShift currentPmask currentWidth currentMask previousShift previousPmask
      previousWidth previousMask sigEnc eraseEnc factT level : ℕ}
    {currentTree previousTree : Lean.RArray ℕ} {upper : ℕ}
    (h : TreeLevelStepRange currentShift currentPmask currentWidth currentMask previousShift
      previousPmask previousWidth previousMask sigEnc eraseEnc factT level currentTree
      previousTree 0 upper) :
    ∀ t < upper, ∀ s ≤ t,
      let active := cert246Data.nilActive level
        (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField sigEnc t))
      Bool.rec (motive := fun _ ↦ ℕ) 0
          (cert246Data.treeAt currentShift currentPmask currentWidth currentMask currentTree
            (cert246Data.triIdx s t)) active =
        Bool.rec (motive := fun _ ↦ ℕ) 0
          (cert246Data.nilTreeEntry sigEnc eraseEnc factT level previousShift previousPmask
            previousWidth previousMask previousTree s t) active :=
  rangeFinish h

/-- Rows with both a checked split-level result and predecessor bound. -/
abbrev LevelResultBoundRange
    (outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (resultTree : Lean.RArray ℕ)
    (lower upper : ℕ) : Prop :=
  ∀ t, lower ≤ t → t < upper → ∀ s ≤ t,
    cert246Data.treeAt pairCs pairPmask pairWidth pairMask resultTree
        (cert246Data.triIdx s t) =
        (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
          shifts pmasks widths masks trees s t).1 ∧
      (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
          shifts pmasks widths masks trees s t).2 < 2 ^ outWidth

/-- One emitted split-level result-and-bound block as a mathematical row range. -/
theorem levelResultBoundBlock
    {outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {resultTree : Lean.RArray ℕ}
    {lower upper index : ℕ}
    (h : cert246Data.nilResultBoundLevelsCheck outWidth pairCs pairPmask pairWidth
      pairMask coeffT maxLevel sigEnc shifts pmasks widths masks trees resultTree
      lower upper index = true)
    (hgeometry : decide (pairPmask + 1 = 2 ^ pairCs) = true)
    (hindex : decide (index = lower * (lower + 1) / 2) = true) :
    LevelResultBoundRange outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel
      sigEnc shifts pmasks widths masks trees resultTree lower upper :=
  nilResultBoundLevelsCheck_sound (of_decide_eq_true hgeometry)
    (by rw [rowsBase_zero]; exact of_decide_eq_true hindex) h

/-- Adjacent split-level result-and-bound ranges splice. -/
theorem levelResultBoundSplice
    {outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {resultTree : Lean.RArray ℕ}
    {lower middle upper : ℕ}
    (left : LevelResultBoundRange outWidth pairCs pairPmask pairWidth pairMask coeffT
      maxLevel sigEnc shifts pmasks widths masks trees resultTree lower middle)
    (right : LevelResultBoundRange outWidth pairCs pairPmask pairWidth pairMask coeffT
      maxLevel sigEnc shifts pmasks widths masks trees resultTree middle upper) :
    LevelResultBoundRange outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel
      sigEnc shifts pmasks widths masks trees resultTree lower upper := by
  intro t hlow hhigh s hst
  by_cases hmiddle : t < middle
  · exact left t hlow hmiddle s hst
  · exact right t (Nat.le_of_not_gt hmiddle) hhigh s hst

/-- Finish a complete split-level result-and-bound range. -/
theorem levelResultBoundFinish
    {outWidth pairCs pairPmask pairWidth pairMask coeffT maxLevel sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {resultTree : Lean.RArray ℕ} {upper : ℕ}
    (h : LevelResultBoundRange outWidth pairCs pairPmask pairWidth pairMask coeffT
      maxLevel sigEnc shifts pmasks widths masks trees resultTree 0 upper) :
    ∀ t < upper, ∀ s ≤ t,
      cert246Data.treeAt pairCs pairPmask pairWidth pairMask resultTree
          (cert246Data.triIdx s t) =
          (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
            shifts pmasks widths masks trees s t).1 ∧
        (cert246Data.nilMomentPairPredLevels outWidth coeffT maxLevel sigEnc
            shifts pmasks widths masks trees s t).2 < 2 ^ outWidth :=
  fun t ht ↦ h t (Nat.zero_le t) ht

open Lean Meta Elab in
/-- Gather the independently packed level-zero table. -/
meta def gatherLevelBaseProof : MetaM Expr :=
  gatherRangeProof "nil_level_base" ``PrimeGaps.Gap246.levelBaseBlock
    ``PrimeGaps.Gap246.levelBaseSplice ``PrimeGaps.Gap246.levelBaseFinish
    #[0, 1, 2, 3, 4, 5] 2

open Lean Meta Elab in
/-- Gather one dependency-isolated independently packed transition level. -/
meta def gatherTreeLevelStepProof (level : ℕ) : MetaM Expr :=
  gatherRangeProof s!"nil_level_step_{level}" ``PrimeGaps.Gap246.treeLevelStepBlock
    ``PrimeGaps.Gap246.treeLevelStepSplice
    ``PrimeGaps.Gap246.treeLevelStepFinish
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 1

open Lean Meta Elab in
/-- Gather the fused split-level result and predecessor bound. -/
meta def gatherLevelResultBoundProof : MetaM Expr :=
  gatherRangeProof "nil_level_result_bound"
    ``PrimeGaps.Gap246.levelResultBoundBlock
    ``PrimeGaps.Gap246.levelResultBoundSplice
    ``PrimeGaps.Gap246.levelResultBoundFinish
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13] 2

open Lean Meta Elab in
/-- The literal level in an independently packed transition goal. -/
meta def goalLevelStepLevel (goal : MVarId) : MetaM ℕ := do
  let some entry := (← instantiateMVars (← goal.getType)).find? fun expression ↦
      expression.isAppOfArity ``cert246Data.nilLevelAt 7 &&
        (expression.getAppArgs[5]!.nat? <|> expression.getAppArgs[5]!.rawNatLit?).isSome
    | throwError "gather_cert246_level_step: no literal nilpotent level in the goal"
  return (entry.getAppArgs[5]!.nat? <|> entry.getAppArgs[5]!.rawNatLit?).get!

open Lean Elab Tactic in
/-- Close the independently packed level-zero goal. -/
elab "gather_cert246_level_base" : tactic =>
  liftMetaFinishingTactic fun goal ↦ do
    goal.assign (← gatherLevelBaseProof)

open Lean Elab Tactic in
/-- Close one independently packed transition-level goal. -/
elab "gather_cert246_level_step" : tactic =>
  liftMetaFinishingTactic fun goal ↦ do
    goal.assign (← gatherTreeLevelStepProof (← goalLevelStepLevel goal))

open Lean Elab Tactic in
/-- Close the fused independently packed result-and-bound goal. -/
elab "gather_cert246_level_result_bound" : tactic =>
  liftMetaFinishingTactic fun goal ↦ do
    goal.assign (← gatherLevelResultBoundProof)

attribute [nolint defsWithUnderscore]
  tacticGather_cert246_level_base tacticGather_cert246_level_step
  tacticGather_cert246_level_result_bound

end PrimeGaps.Gap246
