/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.ResultSound


/-! # Gathering the emitted packed moment blocks -/

@[expose] public section

namespace PrimeGaps.Gap246

/-- Rows `[lower, upper)` of a triangular table agree with their specification. -/
abbrev Range (value specification : ℕ → ℕ → ℕ) (lower upper : ℕ) : Prop :=
  ∀ t, lower ≤ t → t < upper → ∀ s ≤ t, value s t = specification s t

/-- A checked row block, with its cursor geometry and triangular offset discharged by
small kernel decisions. -/
theorem rangeBlock {value specification : ℕ → ℕ → ℕ} {lower upper index : ℕ}
    (sound : index = rowsBase 0 lower → Range value specification lower upper)
    (hindex : decide (index = lower * (lower + 1) / 2) = true) :
    Range value specification lower upper :=
  sound (by rw [rowsBase_zero]; exact of_decide_eq_true hindex)

/-- Adjacent triangular row ranges splice into one range. -/
theorem rangeSplice {value specification : ℕ → ℕ → ℕ}
    {lower middle upper : ℕ} (left : Range value specification lower middle)
    (right : Range value specification middle upper) :
    Range value specification lower upper := by
  grind

/-- A range beginning at zero is the usual bounded-row statement. -/
theorem rangeFinish {value specification : ℕ → ℕ → ℕ} {upper : ℕ}
    (h : Range value specification 0 upper) :
    ∀ t < upper, ∀ s ≤ t, value s t = specification s t :=
  fun t ht ↦ h t (Nat.zero_le t) ht

/-! ## Block-family wrappers -/

/-- Rows of a checked level-zero block. -/
abbrev BaseRange (cs pmask width mask sigEnc : ℕ) (tree : Lean.RArray ℕ)
    (lower upper : ℕ) : Prop :=
  Range
    (fun s t ↦ cert246Data.treeAt cs pmask width mask tree (cert246Data.triIdx s t))
    (fun s t ↦ if cert246Data.sigField sigEnc s = 0 ∧
      cert246Data.sigField sigEnc t = 0 then 1 else 0) lower upper

/-- One emitted level-zero block as a mathematical row range. -/
theorem baseBlock {cs pmask width mask sigEnc : ℕ} {tree : Lean.RArray ℕ}
    {lower upper index : ℕ}
    (h : cert246Data.nilBaseCheck cs pmask width mask sigEnc tree lower upper index = true)
    (hgeometry : decide (pmask + 1 = 2 ^ cs) = true)
    (hindex : decide (index = lower * (lower + 1) / 2) = true) :
    BaseRange cs pmask width mask sigEnc tree lower upper :=
  rangeBlock
    (fun hindex' ↦ nilBaseCheck_sound (of_decide_eq_true hgeometry) hindex' h) hindex

/-- Adjacent emitted level-zero ranges splice. -/
theorem baseSplice {cs pmask width mask sigEnc : ℕ} {tree : Lean.RArray ℕ}
    {lower middle upper : ℕ}
    (left : BaseRange cs pmask width mask sigEnc tree lower middle)
    (right : BaseRange cs pmask width mask sigEnc tree middle upper) :
    BaseRange cs pmask width mask sigEnc tree lower upper :=
  rangeSplice left right

/-- Finish a complete emitted level-zero range. -/
theorem baseFinish {cs pmask width mask sigEnc : ℕ} {tree : Lean.RArray ℕ} {upper : ℕ}
    (h : BaseRange cs pmask width mask sigEnc tree 0 upper) :
    ∀ t < upper, ∀ s ≤ t,
      cert246Data.treeAt cs pmask width mask tree (cert246Data.triIdx s t) =
        if cert246Data.sigField sigEnc s = 0 ∧
            cert246Data.sigField sigEnc t = 0 then 1 else 0 :=
  rangeFinish h

/-- Rows of one checked identity-free transition level. -/
abbrev StepRange (tri cs pmask width mask sigEnc eraseEnc factT level : ℕ)
    (tree : Lean.RArray ℕ) (lower upper : ℕ) : Prop :=
  Range
    (fun s t ↦ cert246Data.treeAt cs pmask width mask tree
      (level * tri + cert246Data.triIdx s t))
    (fun s t ↦ Bool.rec 0
      (cert246Data.nilEntry tri cs pmask width mask eraseEnc factT level tree s t)
      (cert246Data.nilActive level
        (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField sigEnc t)))) lower upper

/-- One emitted transition block as a mathematical row range. -/
theorem stepBlock {tri cs pmask width mask sigEnc eraseEnc factT level : ℕ}
    {tree : Lean.RArray ℕ} {lower upper index : ℕ}
    (h : cert246Data.nilStepCheck tri cs pmask width mask sigEnc eraseEnc factT level tree
      lower upper index = true)
    (hgeometry : decide (pmask + 1 = 2 ^ cs) = true)
    (hindex : decide (index = lower * (lower + 1) / 2) = true) :
    StepRange tri cs pmask width mask sigEnc eraseEnc factT level tree lower upper :=
  rangeBlock
    (fun hindex' ↦ nilStepCheck_sound (of_decide_eq_true hgeometry) hindex' h) hindex

/-- Adjacent emitted transition ranges splice. -/
theorem stepSplice {tri cs pmask width mask sigEnc eraseEnc factT level : ℕ}
    {tree : Lean.RArray ℕ} {lower middle upper : ℕ}
    (left : StepRange tri cs pmask width mask sigEnc eraseEnc factT level tree lower middle)
    (right : StepRange tri cs pmask width mask sigEnc eraseEnc factT level tree middle upper) :
    StepRange tri cs pmask width mask sigEnc eraseEnc factT level tree lower upper :=
  rangeSplice left right

/-- Finish a complete emitted transition range. -/
theorem stepFinish {tri cs pmask width mask sigEnc eraseEnc factT level : ℕ}
    {tree : Lean.RArray ℕ} {upper : ℕ}
    (h : StepRange tri cs pmask width mask sigEnc eraseEnc factT level tree 0 upper) :
    ∀ t < upper, ∀ s ≤ t,
      cert246Data.treeAt cs pmask width mask tree
          (level * tri + cert246Data.triIdx s t) =
        Bool.rec 0
          (cert246Data.nilEntry tri cs pmask width mask eraseEnc factT level tree s t)
          (cert246Data.nilActive level
            (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
              cert246Data.sigCount (cert246Data.sigField sigEnc t))) :=
  rangeFinish h

/-- Rows of the checked final packed-pair table. -/
abbrev ResultRange
    (tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension maxLevel
      sigEnc : ℕ) (tree resultTree : Lean.RArray ℕ) (lower upper : ℕ) : Prop :=
  Range
    (fun s t ↦ cert246Data.treeAt pairCs pairPmask pairWidth pairMask resultTree
      (cert246Data.triIdx s t))
    (fun s t ↦ cert246Data.nilMomentPair tri cs pmask width mask outWidth dimension
      maxLevel sigEnc tree s t) lower upper

/-- One emitted final-result block as a mathematical row range. -/
theorem resultBlock
    {tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension maxLevel
      sigEnc : ℕ} {tree resultTree : Lean.RArray ℕ} {lower upper index : ℕ}
    (h : cert246Data.nilResultCheck tri cs pmask width mask outWidth pairCs pairPmask
      pairWidth pairMask dimension maxLevel sigEnc tree resultTree lower upper index = true)
    (hgeometry : decide (pairPmask + 1 = 2 ^ pairCs) = true)
    (hindex : decide (index = lower * (lower + 1) / 2) = true) :
    ResultRange tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension
      maxLevel sigEnc tree resultTree lower upper :=
  rangeBlock
    (fun hindex' ↦ nilResultCheck_sound (of_decide_eq_true hgeometry) hindex' h) hindex

/-- Adjacent emitted final-result ranges splice. -/
theorem resultSplice
    {tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension maxLevel
      sigEnc : ℕ} {tree resultTree : Lean.RArray ℕ} {lower middle upper : ℕ}
    (left : ResultRange tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask
      dimension maxLevel sigEnc tree resultTree lower middle)
    (right : ResultRange tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask
      dimension maxLevel sigEnc tree resultTree middle upper) :
    ResultRange tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension
      maxLevel sigEnc tree resultTree lower upper :=
  rangeSplice left right

/-- Finish a complete emitted final-result range. -/
theorem resultFinish
    {tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension maxLevel
      sigEnc : ℕ} {tree resultTree : Lean.RArray ℕ} {upper : ℕ}
    (h : ResultRange tri cs pmask width mask outWidth pairCs pairPmask pairWidth pairMask dimension
      maxLevel sigEnc tree resultTree 0 upper) :
    ∀ t < upper, ∀ s ≤ t,
      cert246Data.treeAt pairCs pairPmask pairWidth pairMask resultTree
          (cert246Data.triIdx s t) =
        cert246Data.nilMomentPair tri cs pmask width mask outWidth dimension maxLevel
          sigEnc tree s t :=
  rangeFinish h

/-! ## Raw block gathering -/

open Lean Elab in
/-- Emitted blocks with a consecutive numeric suffix. -/
meta def gatherNames (environment : Environment) (pfx : String) : Array Name := Id.run do
  let mut names := #[]
  let mut block := 0
  while environment.contains (`cert246Data ++ Name.mkSimple s!"{pfx}_{block}") do
    names := names.push (`cert246Data ++ Name.mkSimple s!"{pfx}_{block}")
    block := block + 1
  return names

open Lean in
/-- Arguments of the boolean check on the left side of an emitted theorem. -/
meta def blockArgs (information : ConstantInfo) : Array Expr :=
  (information.type.getAppArgs[1]!).getAppArgs

open Lean Meta Elab in
/-- Splice every emitted row block of one family into a whole-range proof. -/
meta def gatherRangeProof (pfx : String) (block splice finish : Name)
    (sharedIndices : Array ℕ) (sideCount : ℕ) : MetaM Expr := do
  let names := gatherNames (← getEnv) pfx
  if names.isEmpty then
    throwError "gather: no emitted blocks named cert246Data.{pfx}_*"
  let sides := Array.replicate sideCount reflBoolTrue
  let blockProof (name : Name) : MetaM (Array Expr × Expr × Expr × Expr) := do
    let arguments := blockArgs (← getConstInfo name)
    let shared := sharedIndices.map (arguments[·]!)
    let proof := mkAppN (mkConst block)
      (shared ++ #[arguments[arguments.size - 3]!, arguments[arguments.size - 2]!,
        arguments[arguments.size - 1]!, mkConst name] ++ sides)
    return (shared, arguments[arguments.size - 3]!,
      arguments[arguments.size - 2]!, proof)
  let (shared, lower, firstUpper, first) ← blockProof names[0]!
  let mut accumulated := first
  let mut upper := firstUpper
  for index in [1:names.size] do
    let (_, _, nextUpper, proof) ← blockProof names[index]!
    accumulated := mkAppN (mkConst splice)
      (shared ++ #[lower, upper, nextUpper, accumulated, proof])
    upper := nextUpper
  return mkAppN (mkConst finish) (shared ++ #[upper, accumulated])

open Lean Meta Elab in
/-- Gather the complete level-zero table. -/
meta def gatherBaseProof : MetaM Expr :=
  gatherRangeProof "nil_base" ``PrimeGaps.Gap246.baseBlock
    ``PrimeGaps.Gap246.baseSplice ``PrimeGaps.Gap246.baseFinish
    #[0, 1, 2, 3, 4, 5] 2

open Lean Meta Elab in
/-- Gather one complete identity-free transition level. -/
meta def gatherStepProof (level : ℕ) : MetaM Expr :=
  gatherRangeProof s!"nil_step_{level}" ``PrimeGaps.Gap246.stepBlock
    ``PrimeGaps.Gap246.stepSplice ``PrimeGaps.Gap246.stepFinish
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9] 2

open Lean Meta Elab in
/-- Gather the complete final packed-pair table. -/
meta def gatherResultProof : MetaM Expr :=
  gatherRangeProof "nil_result" ``PrimeGaps.Gap246.resultBlock
    ``PrimeGaps.Gap246.resultSplice ``PrimeGaps.Gap246.resultFinish
    #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14] 2

open Lean Meta Elab in
/-- The literal level in a transition goal. -/
meta def goalStepLevel (goal : MVarId) : MetaM ℕ := do
  let some entry := (← instantiateMVars (← goal.getType)).find? fun expression ↦
      expression.isAppOfArity ``cert246Data.nilEntry 11 &&
        (expression.getAppArgs[7]!.nat? <|> expression.getAppArgs[7]!.rawNatLit?).isSome
    | throwError "gather_cert246_step: no literal nilpotent level in the goal"
  return (entry.getAppArgs[7]!.nat? <|> entry.getAppArgs[7]!.rawNatLit?).get!

open Lean Elab Tactic in
/-- Close a whole-range level-zero goal from emitted row blocks. -/
elab "gather_cert246_base" : tactic =>
  liftMetaFinishingTactic fun goal ↦ do
    goal.assign (← gatherBaseProof)

open Lean Elab Tactic in
/-- Close a whole-range transition goal from the emitted blocks of its literal level. -/
elab "gather_cert246_step" : tactic =>
  liftMetaFinishingTactic fun goal ↦ do
    goal.assign (← gatherStepProof (← goalStepLevel goal))

open Lean Elab Tactic in
/-- Close the whole-range final-result goal from emitted row blocks. -/
elab "gather_cert246_result" : tactic =>
  liftMetaFinishingTactic fun goal ↦ do
    goal.assign (← gatherResultProof)

attribute [nolint defsWithUnderscore]
  tacticGather_cert246_base tacticGather_cert246_step tacticGather_cert246_result

end PrimeGaps.Gap246
