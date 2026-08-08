/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.LHS

local notation "ℕ" => Nat

/-! # First-order sparse RHS kernel -/

@[expose] public section

namespace cert246Data

/-- One 32-bit RHS feature descriptor. -/
noncomputable def rhsFeatureField (featureEnc feature : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight featureEnc (Nat.shiftLeft feature 5)) 4294967295

/-- Signature component of one RHS feature. -/
noncomputable def rhsFeatureSignature (field : ℕ) : ℕ := Nat.land field 511

/-- Residual-degree component of one RHS feature. -/
noncomputable def rhsFeatureResidual (field : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight field 9) 63

/-- Radial-degree component of one RHS feature. -/
noncomputable def rhsFeatureRadial (field : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight field 15) 63

/-- Check the feature key selected by one label-and-erasure lookup. -/
noncomputable def rhsFeatureKeyAt
    (featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask labelEnc featureEnc : ℕ)
    (sourceTree eraseTree : Lean.RArray ℕ) (label exponent : ℕ) : Bool :=
  let labelField := labelField labelEnc label
  let sourceSignature := labelSignature labelField
  let location := treeAt sourceCs sourcePmask 16 65535 sourceTree
    (Nat.add (Nat.mul label (Nat.add degreeBound 1)) exponent)
  let erasedSignature := treeAt eraseCs erasePmask 16 65535 eraseTree
    (Nat.add (Nat.mul sourceSignature (Nat.add degreeBound 1)) exponent)
  let featureField := rhsFeatureField featureEnc location
  Bool.and' (Nat.blt location featureCount)
    (Bool.and' (Nat.beq (rhsFeatureSignature featureField) erasedSignature)
      ((Nat.beq (rhsFeatureResidual featureField) (Nat.sub (labelDegree labelField) exponent))
        && (Nat.beq (rhsFeatureRadial featureField)
          (Nat.add (Nat.add (labelA labelField) exponent) 1))))

/-- Check the identity and every represented signature-part erasure of one label. -/
noncomputable def rhsFeatureKeyLabelCheck
    (featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask sigEnc labelEnc featureEnc
      : ℕ) (sourceTree eraseTree : Lean.RArray ℕ) (label : ℕ) : Bool :=
  let labelField := labelField labelEnc label
  let signatureField := sigField sigEnc (labelSignature labelField)
  (rhsFeatureKeyAt featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask labelEnc
      featureEnc sourceTree eraseTree label 0)
    && (Nat.rec (motive := fun _ ↦ ℕ → Bool)
      (fun _ ↦ true)
      (fun _ inductionHypothesis position ↦
        Bool.rec false (inductionHypothesis position.succ)
          (rhsFeatureKeyAt featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask
            labelEnc featureEnc sourceTree eraseTree label
            (Nat.mul 2 (sigNib signatureField position))))
      (sigCount signatureField) 0)

/-- Check a consecutive range of label-and-erasure RHS feature keys. -/
noncomputable def rhsFeatureKeysCheck
    (featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask sigEnc labelEnc featureEnc
      lower upper : ℕ) (sourceTree eraseTree : Lean.RArray ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis label ↦
      Bool.rec false (inductionHypothesis label.succ)
        (rhsFeatureKeyLabelCheck featureCount degreeBound sourceCs sourcePmask eraseCs erasePmask
          sigEnc labelEnc featureEnc sourceTree eraseTree label))
    (Nat.sub upper lower) lower

/-- Three natural accumulators used by the carry-free global RHS weight check.  The first
component is a magnitude bound; the other two are packed positive and negative lanes. -/
structure RhsWeightLanes where
  /-- The unsigned contribution to the weight bound. -/
  bound : ℕ
  /-- The positive lane of the signed weight contribution. -/
  positive : ℕ
  /-- The negative lane of the signed weight contribution. -/
  negative : ℕ

/-- Add one signed magnitude to a fixed-width lane selected by its feature location. -/
noncomputable def rhsWeightLanesAdd (laneWidth sign magnitude location : ℕ)
    (lanes : RhsWeightLanes) : RhsWeightLanes :=
  let shifted := Nat.shiftLeft magnitude (Nat.mul laneWidth location)
  if sign = 0 then
    { bound := Nat.add lanes.bound magnitude
      positive := Nat.add lanes.positive shifted
      negative := lanes.negative }
  else
    { bound := Nat.add lanes.bound magnitude
      positive := lanes.positive
      negative := Nat.add lanes.negative shifted }

/-- Add one label-and-erasure transition to the packed source lanes. -/
noncomputable def rhsSourceWeightLanesAdd
    (degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth labelEnc : ℕ)
    (sourceTree coefficientTree : Lean.RArray ℕ) (label exponent : ℕ)
    (lanes : RhsWeightLanes) : RhsWeightLanes :=
  let labelField := labelField labelEnc label
  let location := treeAt sourceCs sourcePmask 16 65535 sourceTree
    (Nat.add (Nat.mul label (Nat.add degreeBound 1)) exponent)
  let coefficient := treeAt coefficientCs coefficientPmask coefficientWidth coefficientMask
    coefficientTree label
  let magnitude := Nat.mul
    (Nat.mul (Nat.mul coefficient (factorialFold exponent))
      (factorialFold (labelA labelField)))
    (descFactorialFold (Nat.add degreeBound 1)
      (Nat.sub degreeBound (Nat.add (labelA labelField) exponent)))
  rhsWeightLanesAdd laneWidth (labelSign labelField) magnitude location lanes

/-- Test whether an exponent is the identity erasure or occurs among the represented signature
parts.  Scanning the bounded exponent alphabet avoids constructing or deduplicating a list. -/
noncomputable def rhsSignatureHasExponent (signatureField exponent : ℕ) : Bool :=
  Bool.or' (Nat.beq exponent 0)
    (Nat.rec (motive := fun _ ↦ ℕ → Bool)
      (fun _ ↦ false)
      (fun _ inductionHypothesis position ↦
        Bool.or' (Nat.beq (Nat.mul 2 (sigNib signatureField position)) exponent)
          (inductionHypothesis position.succ))
      (sigCount signatureField) 0)

/-- Generalized bounded exponent scan used by the global source-weight fold. -/
noncomputable def rhsSourceWeightExponentLanes
    (degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth labelEnc : ℕ)
    (sourceTree coefficientTree : Lean.RArray ℕ) (label signatureField : ℕ) :
    ℕ → ℕ → RhsWeightLanes → RhsWeightLanes
  | 0, _, lanes => lanes
  | count + 1, exponent, lanes =>
      let next := if rhsSignatureHasExponent signatureField exponent then
        rhsSourceWeightLanesAdd degreeBound sourceCs sourcePmask coefficientCs
          coefficientPmask coefficientWidth coefficientMask laneWidth labelEnc sourceTree
          coefficientTree label exponent lanes
      else lanes
      rhsSourceWeightExponentLanes degreeBound sourceCs sourcePmask coefficientCs
        coefficientPmask coefficientWidth coefficientMask laneWidth labelEnc sourceTree
        coefficientTree label signatureField count exponent.succ next

/-- Scan the bounded exponent alphabet of one source label, adding exactly its identity erasure
and its distinct represented exponents. -/
noncomputable def rhsSourceWeightLabelLanes
    (degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth sigEnc labelEnc : ℕ)
    (sourceTree coefficientTree : Lean.RArray ℕ) (label : ℕ)
    (lanes : RhsWeightLanes) : RhsWeightLanes :=
  let labelField := labelField labelEnc label
  let signatureField := sigField sigEnc (labelSignature labelField)
  rhsSourceWeightExponentLanes degreeBound sourceCs sourcePmask coefficientCs coefficientPmask
    coefficientWidth coefficientMask laneWidth labelEnc sourceTree coefficientTree label
    signatureField (Nat.add degreeBound 1) 0 lanes

/-- Generalized source-label scan used by the global source-weight fold. -/
noncomputable def rhsSourceWeightLabelRangeLanes
    (degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth sigEnc labelEnc : ℕ)
    (sourceTree coefficientTree : Lean.RArray ℕ) : ℕ → ℕ → RhsWeightLanes
  | 0, _ => { bound := 0, positive := 0, negative := 0 }
  | count + 1, label =>
      rhsSourceWeightLabelLanes degreeBound sourceCs sourcePmask coefficientCs coefficientPmask
        coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree coefficientTree label
        (rhsSourceWeightLabelRangeLanes degreeBound sourceCs sourcePmask coefficientCs
          coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
          coefficientTree count label.succ)

/-- Componentwise addition of two independently accumulated weight-lane blocks. -/
noncomputable def rhsWeightLanesMerge
    (left right : RhsWeightLanes) : RhsWeightLanes :=
  { bound := Nat.add left.bound right.bound
    positive := Nat.add left.positive right.positive
    negative := Nat.add left.negative right.negative }

/-- Scan a fixed number of equal-sized consecutive label blocks. -/
noncomputable def rhsSourceWeightBlockRangeLanes
    (degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth sigEnc labelEnc : ℕ)
    (sourceTree coefficientTree : Lean.RArray ℕ) (blockSize : ℕ) :
    ℕ → ℕ → RhsWeightLanes
  | 0, _ => { bound := 0, positive := 0, negative := 0 }
  | count + 1, cursor =>
      rhsWeightLanesMerge
        (rhsSourceWeightLabelRangeLanes degreeBound sourceCs sourcePmask coefficientCs
          coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
          coefficientTree blockSize cursor)
        (rhsSourceWeightBlockRangeLanes degreeBound sourceCs sourcePmask coefficientCs
          coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
          coefficientTree blockSize count (Nat.add cursor blockSize))

/-- Accumulate source labels through bounded leaf scans instead of one deep linear reduction. -/
noncomputable def rhsSourceWeightChunkedLanes
    (labelCount degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth sigEnc labelEnc blockSize : ℕ)
    (sourceTree coefficientTree : Lean.RArray ℕ) : RhsWeightLanes :=
  Bool.rec
    (rhsSourceWeightLabelRangeLanes degreeBound sourceCs sourcePmask coefficientCs
      coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
      coefficientTree labelCount 0)
    (rhsWeightLanesMerge
      (rhsSourceWeightBlockRangeLanes degreeBound sourceCs sourcePmask coefficientCs
        coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
        coefficientTree blockSize (labelCount / blockSize) 0)
      (rhsSourceWeightLabelRangeLanes degreeBound sourceCs sourcePmask coefficientCs
        coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
        coefficientTree (labelCount % blockSize)
        (Nat.mul (labelCount / blockSize) blockSize)))
    (Nat.blt 0 blockSize)

/-- Accumulate every canonical source transition into carry-free fixed-width lanes. -/
noncomputable def rhsSourceWeightLanes
    (labelCount degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth sigEnc labelEnc : ℕ)
    (sourceTree coefficientTree : Lean.RArray ℕ) : RhsWeightLanes :=
  rhsSourceWeightLabelRangeLanes degreeBound sourceCs sourcePmask coefficientCs coefficientPmask
    coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree coefficientTree
    labelCount 0

/-- Generalized stored-feature scan used by the expected-weight fold. -/
noncomputable def rhsExpectedWeightRangeLanes
    (weightCs weightPmask weightWidth weightMask laneWidth : ℕ)
    (weightTree : Lean.RArray ℕ) : ℕ → ℕ → RhsWeightLanes
  | 0, _ => { bound := 0, positive := 0, negative := 0 }
  | count + 1, feature =>
      let lanes := rhsExpectedWeightRangeLanes weightCs weightPmask weightWidth weightMask
        laneWidth weightTree count feature.succ
      let value := treeAt weightCs weightPmask weightWidth weightMask weightTree feature
      let magnitude := signedMagnitude value
      let shifted := Nat.shiftLeft magnitude (Nat.mul laneWidth feature)
      if signedSign value = 0 then
        { bound := max lanes.bound magnitude
          positive := Nat.add lanes.positive shifted
          negative := lanes.negative }
      else
        { bound := max lanes.bound magnitude
          positive := lanes.positive
          negative := Nat.add lanes.negative shifted }

/-- Combine independently accumulated expected-weight blocks, taking the largest digit bound. -/
noncomputable def rhsExpectedWeightLanesMerge
    (left right : RhsWeightLanes) : RhsWeightLanes :=
  { bound := max left.bound right.bound
    positive := Nat.add left.positive right.positive
    negative := Nat.add left.negative right.negative }

/-- Scan a fixed number of equal-sized consecutive expected-feature blocks. -/
noncomputable def rhsExpectedWeightBlockRangeLanes
    (weightCs weightPmask weightWidth weightMask laneWidth : ℕ)
    (weightTree : Lean.RArray ℕ) (blockSize : ℕ) : ℕ → ℕ → RhsWeightLanes
  | 0, _ => { bound := 0, positive := 0, negative := 0 }
  | count + 1, cursor =>
      rhsExpectedWeightLanesMerge
        (rhsExpectedWeightRangeLanes weightCs weightPmask weightWidth weightMask laneWidth
          weightTree blockSize cursor)
        (rhsExpectedWeightBlockRangeLanes weightCs weightPmask weightWidth weightMask laneWidth
          weightTree blockSize count (Nat.add cursor blockSize))

/-- Pack expected weights through bounded leaf scans instead of one deep linear reduction. -/
noncomputable def rhsExpectedWeightChunkedLanes
    (featureCount weightCs weightPmask weightWidth weightMask laneWidth blockSize : ℕ)
    (weightTree : Lean.RArray ℕ) : RhsWeightLanes :=
  Bool.rec
    (rhsExpectedWeightRangeLanes weightCs weightPmask weightWidth weightMask laneWidth weightTree
      featureCount 0)
    (rhsExpectedWeightLanesMerge
      (rhsExpectedWeightBlockRangeLanes weightCs weightPmask weightWidth weightMask laneWidth
        weightTree blockSize (featureCount / blockSize) 0)
      (rhsExpectedWeightRangeLanes weightCs weightPmask weightWidth weightMask laneWidth weightTree
        (featureCount % blockSize) (Nat.mul (featureCount / blockSize) blockSize)))
    (Nat.blt 0 blockSize)

/-- Pack the proposed feature weights into the same fixed-width positive and negative lanes.
Here `bound` records the largest stored magnitude rather than their sum. -/
noncomputable def rhsExpectedWeightLanes
    (featureCount weightCs weightPmask weightWidth weightMask laneWidth : ℕ)
    (weightTree : Lean.RArray ℕ) : RhsWeightLanes :=
  rhsExpectedWeightRangeLanes weightCs weightPmask weightWidth weightMask laneWidth weightTree
    featureCount 0

/-- A carry-free equality of two packed-natural lanes checks every RHS feature-weight fiber at
once.  The lane width and every mathematical dimension remain explicit parameters. -/
noncomputable def rhsWeightEncodingCheck
    (labelCount featureCount degreeBound sourceCs sourcePmask coefficientCs coefficientPmask
      coefficientWidth coefficientMask weightCs weightPmask weightWidth weightMask laneWidth
      sigEnc labelEnc : ℕ)
    (sourceTree coefficientTree weightTree : Lean.RArray ℕ) : Bool :=
  let source := rhsSourceWeightLanes labelCount degreeBound sourceCs sourcePmask coefficientCs
    coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
    coefficientTree
  let expected := rhsExpectedWeightLanes featureCount weightCs weightPmask weightWidth weightMask
    laneWidth weightTree
  Bool.and' (Nat.blt (Nat.add source.bound expected.bound) (Nat.pow 2 laneWidth))
    (Nat.beq (Nat.add source.positive expected.negative)
      (Nat.add source.negative expected.positive))

/-- Read one independently proposed partial weight-lane record. -/
noncomputable def rhsWeightCheckpointAt (bound positive negative : Lean.RArray ℕ)
    (block : ℕ) : RhsWeightLanes :=
  { bound := bound.get block, positive := positive.get block, negative := negative.get block }

/-- Compare all fields of a computed weight-lane record with one proposed checkpoint. -/
noncomputable def rhsWeightLanesEqCheck (actual expected : RhsWeightLanes) : Bool :=
  Bool.and' (Nat.beq actual.bound expected.bound)
    (Bool.and' (Nat.beq actual.positive expected.positive)
      (Nat.beq actual.negative expected.negative))

/-- Check one full source-label block, or the final remainder block. -/
noncomputable def rhsSourceWeightCheckpointBlockCheck
    (labelCount degreeBound sourceCs sourcePmask coefficientCs coefficientPmask coefficientWidth
      coefficientMask laneWidth sigEnc labelEnc blockSize block : ℕ)
    (sourceTree coefficientTree checkpointBound checkpointPositive checkpointNegative :
      Lean.RArray ℕ) : Bool :=
  let fullBlockCount := labelCount / blockSize
  let isFull := Nat.blt block fullBlockCount
  let count := Bool.rec (labelCount % blockSize) blockSize isFull
  let cursor := Bool.rec (Nat.mul fullBlockCount blockSize) (Nat.mul block blockSize) isFull
  rhsWeightLanesEqCheck
    (rhsSourceWeightLabelRangeLanes degreeBound sourceCs sourcePmask coefficientCs
      coefficientPmask coefficientWidth coefficientMask laneWidth sigEnc labelEnc sourceTree
      coefficientTree count cursor)
    (rhsWeightCheckpointAt checkpointBound checkpointPositive checkpointNegative block)

/-- Check one full stored-feature block, or the final remainder block. -/
noncomputable def rhsExpectedWeightCheckpointBlockCheck
    (featureCount weightCs weightPmask weightWidth weightMask laneWidth blockSize block : ℕ)
    (weightTree checkpointBound checkpointPositive checkpointNegative : Lean.RArray ℕ) : Bool :=
  let fullBlockCount := featureCount / blockSize
  let isFull := Nat.blt block fullBlockCount
  let count := Bool.rec (featureCount % blockSize) blockSize isFull
  let cursor := Bool.rec (Nat.mul fullBlockCount blockSize) (Nat.mul block blockSize) isFull
  rhsWeightLanesEqCheck
    (rhsExpectedWeightRangeLanes weightCs weightPmask weightWidth weightMask laneWidth weightTree
      count cursor)
    (rhsWeightCheckpointAt checkpointBound checkpointPositive checkpointNegative block)

/-- Merge a consecutive range of proposed source checkpoints. -/
noncomputable def rhsSourceWeightCheckpointFold
    (bound positive negative : Lean.RArray ℕ) : ℕ → ℕ → RhsWeightLanes
  | 0, _ => { bound := 0, positive := 0, negative := 0 }
  | count + 1, block =>
      rhsWeightLanesMerge (rhsWeightCheckpointAt bound positive negative block)
        (rhsSourceWeightCheckpointFold bound positive negative count block.succ)

/-- Merge a consecutive range of proposed expected-weight checkpoints. -/
noncomputable def rhsExpectedWeightCheckpointFold
    (bound positive negative : Lean.RArray ℕ) : ℕ → ℕ → RhsWeightLanes
  | 0, _ => { bound := 0, positive := 0, negative := 0 }
  | count + 1, block =>
      rhsExpectedWeightLanesMerge (rhsWeightCheckpointAt bound positive negative block)
        (rhsExpectedWeightCheckpointFold bound positive negative count block.succ)

/-- Check carry freedom and signed equality after the independently verified blocks are merged. -/
noncomputable def rhsWeightCheckpointBalanceCheck
    (laneWidth sourceFullBlockCount expectedFullBlockCount : ℕ)
    (sourceBound sourcePositive sourceNegative expectedBound expectedPositive expectedNegative :
      Lean.RArray ℕ) : Bool :=
  let source := rhsWeightLanesMerge
    (rhsSourceWeightCheckpointFold sourceBound sourcePositive sourceNegative
      sourceFullBlockCount 0)
    (rhsWeightCheckpointAt sourceBound sourcePositive sourceNegative sourceFullBlockCount)
  let expected := rhsExpectedWeightLanesMerge
    (rhsExpectedWeightCheckpointFold expectedBound expectedPositive expectedNegative
      expectedFullBlockCount 0)
    (rhsWeightCheckpointAt expectedBound expectedPositive expectedNegative
      expectedFullBlockCount)
  Bool.and' (Nat.blt (Nat.add source.bound expected.bound) (Nat.pow 2 laneWidth))
    (Nat.beq (Nat.add source.positive expected.negative)
      (Nat.add source.negative expected.positive))

/-- Check that every feature signature in a consecutive range is in bounds. -/
noncomputable def rhsFeatureSignatureRangeCheck
    (signatureCount featureEnc lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis feature ↦
      Bool.rec false (inductionHypothesis feature.succ)
        (Nat.blt (rhsFeatureSignature (rhsFeatureField featureEnc feature)) signatureCount))
    (Nat.sub upper lower) lower

/-- Check a consecutive range of packed sparse RHS-transform keys. -/
noncomputable def rhsKeysRangeCheck
    (groupCount signatureCount keyEnc lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis entry ↦
      let field := keyField keyEnc entry
      Bool.rec false (inductionHypothesis entry.succ)
        (Bool.and' (Nat.blt (keyGroup field) groupCount)
          (Nat.blt (keyTarget field) signatureCount)))
    (Nat.sub upper lower) lower

/-- Check a consecutive range of group rows in the sparse RHS location index. -/
noncomputable def rhsLocationIndexRangeCheck
    (signatureCount entryCount locationCs locationPmask keyEnc : ℕ)
    (locationTree : Lean.RArray ℕ) (lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ groupHypothesis group ↦
      Bool.rec false (groupHypothesis group.succ)
        (Nat.rec (motive := fun _ ↦ ℕ → Bool)
          (fun _ ↦ true)
          (fun _ targetHypothesis target ↦
            let location := treeAt locationCs locationPmask 16 65535 locationTree
              (Nat.add (Nat.mul group signatureCount) target)
            let key := keyField keyEnc (Nat.sub location 1)
            let valid := Bool.rec
              (Bool.and' (Nat.ble location entryCount)
                (Bool.and' (Nat.beq (keyGroup key) group)
                  (Nat.beq (keyTarget key) target)))
              true (Nat.beq location 0)
            Bool.rec false (targetHypothesis target.succ) valid)
          signatureCount 0))
    (Nat.sub upper lower) lower

/-- Check all sparse locations queried by the smaller-side contraction of two RHS groups. -/
noncomputable def rhsSupportPairCheck
    (signatureCount featureEnc groupEnc locationCs locationPmask : ℕ)
    (locationTree : Lean.RArray ℕ) (left right : ℕ) : Bool :=
  let leftField := groupField groupEnc left
  let rightField := groupField groupEnc right
  let useLeft := Nat.ble (groupSize leftField) (groupSize rightField)
  let sourceField := Bool.rec rightField leftField useLeft
  let transformGroup := Bool.rec left right useLeft
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis cursor ↦
      let featureField := rhsFeatureField featureEnc cursor
      let target := rhsFeatureSignature featureField
      Bool.rec false (inductionHypothesis cursor.succ)
        (Nat.blt 0 (treeAt locationCs locationPmask 16 65535 locationTree
          (Nat.add (Nat.mul transformGroup signatureCount) target))))
    (groupSize sourceField) (groupStart sourceField)

/-- Check every smaller-side sparse-support query made by one RHS row. -/
noncomputable def rhsSupportRowCheck
    (groupCount signatureCount featureEnc groupEnc locationCs locationPmask : ℕ)
    (locationTree : Lean.RArray ℕ) (left : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis right ↦
      Bool.rec false (inductionHypothesis right.succ)
        (rhsSupportPairCheck signatureCount featureEnc groupEnc locationCs locationPmask
          locationTree left right))
    (Nat.sub groupCount left) left

/-- Boundary value of the cleared radial factor at radial degree zero. -/
noncomputable def rhsRadialBoundary (dimension epsilonDenominator q : ℕ) : ℕ :=
  Nat.mul
    (Nat.mul (Nat.pow epsilonDenominator (Nat.sub (Nat.add (Nat.mul 2 dimension) 1) q))
      (Nat.pow (Nat.sub epsilonDenominator 1) q))
    (descFactorialFold (Nat.add (Nat.mul 2 dimension) 1)
      (Nat.sub (Nat.add (Nat.mul 2 dimension) 1) q))

/-- Check one stored radial-factor entry by its boundary value or local recurrence. -/
noncomputable def rhsRadialEntryCheck
    (dimension epsilonDenominator radialDimension radialCs radialPmask radialWidth radialMask
      index : ℕ) (radialTree : Lean.RArray ℕ) : Bool :=
  let q := index / radialDimension
  let e := index % radialDimension
  let value := treeAt radialCs radialPmask radialWidth radialMask radialTree index
  Bool.rec true
    (Bool.rec
      (Nat.beq
        (Nat.add (Nat.mul epsilonDenominator value)
          (Nat.mul (Nat.mul epsilonDenominator q)
            (treeAt radialCs radialPmask radialWidth radialMask radialTree
              (Nat.add (Nat.mul (Nat.add q 1) radialDimension) (Nat.sub e 1)))))
        (Nat.mul (Nat.add epsilonDenominator 1)
          (treeAt radialCs radialPmask radialWidth radialMask radialTree
            (Nat.add (Nat.mul q radialDimension) (Nat.sub e 1)))))
      (Nat.beq value (rhsRadialBoundary dimension epsilonDenominator q))
      (Nat.beq e 0))
    (Bool.and' (Nat.ble (Nat.sub dimension 1) q)
      (Nat.ble (Nat.add q e) (Nat.add (Nat.mul 2 dimension) 1)))

/-- Check a consecutive range of stored radial-factor recurrence entries. -/
noncomputable def rhsRadialCheck
    (dimension epsilonDenominator radialDimension radialCs radialPmask radialWidth radialMask
      lower upper : ℕ) (radialTree : Lean.RArray ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis index ↦
      Bool.rec false (inductionHypothesis index.succ)
        (rhsRadialEntryCheck dimension epsilonDenominator radialDimension radialCs radialPmask
          radialWidth radialMask index radialTree))
    (Nat.sub upper lower) lower

/-- Low predecessor-moment lane of one unordered signature pair. -/
noncomputable def rhsMomentPred
    (pairCs pairPmask pairWidth pairMask outMask : ℕ)
    (pairTree : Lean.RArray ℕ) (left right : ℕ) : ℕ :=
  Nat.land
    (treeAt pairCs pairPmask pairWidth pairMask pairTree (triIdx left right)) outMask

/-- Direct signed predecessor-moment transform of one RHS group at one target signature. -/
noncomputable def rhsTransformValue
    (featureEnc groupEnc weightCs weightPmask weightWidth weightMask pairCs pairPmask pairWidth
      pairMask outMask : ℕ)
    (weightTree pairTree : Lean.RArray ℕ) (group target : ℕ) : ℕ :=
  let groupField := groupField groupEnc group
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ)
    (fun _ positive negative ↦ signedEncode positive negative)
    (fun _ inductionHypothesis cursor positive negative ↦
      let featureField := rhsFeatureField featureEnc cursor
      let weight := treeAt weightCs weightPmask weightWidth weightMask weightTree cursor
      let term := Nat.mul (signedMagnitude weight)
        (rhsMomentPred pairCs pairPmask pairWidth pairMask outMask pairTree target
          (rhsFeatureSignature featureField))
      Bool.rec
        (inductionHypothesis cursor.succ positive (Nat.add negative term))
        (inductionHypothesis cursor.succ (Nat.add positive term) negative)
        (Nat.beq (signedSign weight) 0))
    (groupSize groupField) (groupStart groupField) 0 0

/-- Check a consecutive range of stored sparse RHS transform entries. -/
noncomputable def rhsTransformCheck
    (transformCs transformPmask transformWidth transformMask featureEnc groupEnc keyEnc weightCs
      weightPmask weightWidth weightMask pairCs pairPmask pairWidth pairMask outMask : ℕ)
    (transformTree weightTree pairTree : Lean.RArray ℕ) (lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis entry ↦
      let key := keyField keyEnc entry
      Bool.rec false (inductionHypothesis entry.succ)
        (Nat.beq (treeAt transformCs transformPmask transformWidth transformMask
          transformTree entry)
          (rhsTransformValue featureEnc groupEnc weightCs weightPmask weightWidth weightMask pairCs
            pairPmask pairWidth pairMask outMask weightTree pairTree (keyGroup key)
            (keyTarget key))))
    (Nat.sub upper lower) lower

/-- Stored signed RHS transform through a one-based location table. -/
noncomputable def rhsTransformAt
    (signatureCount locationCs locationPmask transformCs transformPmask transformWidth
      transformMask : ℕ) (locationTree transformTree : Lean.RArray ℕ)
    (group target : ℕ) : ℕ :=
  let location := treeAt locationCs locationPmask 16 65535 locationTree
    (Nat.add (Nat.mul group signatureCount) target)
  treeAt transformCs transformPmask transformWidth transformMask transformTree
    (Nat.sub location 1)

/-- Sparse contraction between two RHS degree groups. -/
noncomputable def rhsContractionValue
    (signatureCount featureEnc groupEnc locationCs locationPmask transformCs transformPmask
      transformWidth transformMask weightCs weightPmask weightWidth weightMask : ℕ)
    (locationTree transformTree weightTree : Lean.RArray ℕ) (left right : ℕ) : ℕ :=
  let leftField := groupField groupEnc left
  let rightField := groupField groupEnc right
  let useLeft := Nat.ble (groupSize leftField) (groupSize rightField)
  let sourceField := Bool.rec rightField leftField useLeft
  let transformGroup := Bool.rec left right useLeft
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ)
    (fun _ positive negative ↦ signedEncode positive negative)
    (fun _ inductionHypothesis cursor positive negative ↦
      let featureField := rhsFeatureField featureEnc cursor
      let weight := treeAt weightCs weightPmask weightWidth weightMask weightTree cursor
      let transform := rhsTransformAt signatureCount locationCs locationPmask transformCs
        transformPmask transformWidth transformMask locationTree transformTree transformGroup
        (rhsFeatureSignature featureField)
      let term := Nat.mul (signedMagnitude weight) (signedMagnitude transform)
      Bool.rec
        (inductionHypothesis cursor.succ positive (Nat.add negative term))
        (inductionHypothesis cursor.succ (Nat.add positive term) negative)
        (Nat.beq (signedSign weight) (signedSign transform)))
    (groupSize sourceField) (groupStart sourceField) 0 0

/-- One signed upper-triangular RHS group row. -/
noncomputable def rhsRowValue
    (dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask weightCs weightPmask
      weightWidth weightMask radialCs radialPmask radialWidth radialMask : ℕ)
    (locationTree transformTree weightTree radialTree : Lean.RArray ℕ) (left : ℕ) : ℕ :=
  let leftField := groupField groupEnc left
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ)
    (fun _ positive negative ↦ signedEncode positive negative)
    (fun _ inductionHypothesis right positive negative ↦
      let rightField := groupField groupEnc right
      let contraction := rhsContractionValue signatureCount featureEnc groupEnc locationCs
        locationPmask transformCs transformPmask transformWidth transformMask weightCs weightPmask
        weightWidth weightMask locationTree transformTree weightTree left right
      let q := Nat.add (Nat.add (Nat.sub dimension 1) (groupLowDegree leftField))
        (groupLowDegree rightField)
      let e := Nat.add (groupHighDegree leftField) (groupHighDegree rightField)
      let radial := treeAt radialCs radialPmask radialWidth radialMask radialTree
        (Nat.add (Nat.mul q radialDimension) e)
      let factor := Bool.rec radial (Nat.mul 2 radial) (Nat.blt left right)
      let term := Nat.mul factor (signedMagnitude contraction)
      Bool.rec
        (inductionHypothesis right.succ positive (Nat.add negative term))
        (inductionHypothesis right.succ (Nat.add positive term) negative)
        (Nat.beq (signedSign contraction) 0))
    (Nat.sub groupCount left) left 0 0

/-- Check a consecutive range of final sparse RHS rows. -/
noncomputable def rhsRowCheck
    (dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth
      rowMask weightCs weightPmask weightWidth weightMask radialCs radialPmask radialWidth
      radialMask : ℕ)
    (locationTree transformTree rowTree weightTree radialTree : Lean.RArray ℕ)
    (lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis left ↦
      Bool.rec false (inductionHypothesis left.succ)
        ((Nat.beq (treeAt rowCs rowPmask rowWidth rowMask rowTree left)
            (rhsRowValue dimension groupCount signatureCount radialDimension featureEnc groupEnc
              locationCs locationPmask transformCs transformPmask transformWidth transformMask
              weightCs weightPmask weightWidth weightMask radialCs radialPmask radialWidth
              radialMask locationTree transformTree weightTree radialTree left))
          && (rhsSupportRowCheck groupCount signatureCount featureEnc groupEnc locationCs locationPmask
            locationTree left)))
    (Nat.sub upper lower) lower

end cert246Data
