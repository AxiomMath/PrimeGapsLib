/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.Core

local notation "ℕ" => Nat

/-! # First-order sparse LHS kernel -/

@[expose] public section

namespace cert246Data

/-- Label index at one position of the flattened LHS member permutation. -/
noncomputable def lhsMember (memberEnc position : ℕ) : ℕ :=
  Nat.land (Nat.shiftRight memberEnc (Nat.shiftLeft position 4)) 65535

/-- Check a consecutive range of packed sparse-transform keys. -/
noncomputable def lhsKeysRangeCheck
    (groupCount signatureCount keyEnc lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis entry ↦
      let field := keyField keyEnc entry
      Bool.rec false (inductionHypothesis entry.succ)
        (Bool.and' (Nat.blt (keyGroup field) groupCount)
          (Nat.blt (keyTarget field) signatureCount)))
    (Nat.sub upper lower) lower

/-- Check a consecutive range of group rows in the sparse LHS location index. -/
noncomputable def lhsLocationIndexRangeCheck
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

/-- Check all sparse locations queried by the smaller-side LHS contraction of two groups. -/
noncomputable def lhsSupportPairCheck
    (signatureCount memberEnc labelEnc groupEnc locationCs locationPmask : ℕ)
    (locationTree : Lean.RArray ℕ) (left right : ℕ) : Bool :=
  let leftField := groupField groupEnc left
  let rightField := groupField groupEnc right
  let useLeft := Nat.ble (groupSize leftField) (groupSize rightField)
  let sourceField := Bool.rec rightField leftField useLeft
  let transformGroup := Bool.rec left right useLeft
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis cursor ↦
      let label := lhsMember memberEnc cursor
      let target := labelSignature (labelField labelEnc label)
      Bool.rec false (inductionHypothesis cursor.succ)
        (Nat.blt 0 (treeAt locationCs locationPmask 16 65535 locationTree
          (Nat.add (Nat.mul transformGroup signatureCount) target))))
    (groupSize sourceField) (groupStart sourceField)

/-- Check every smaller-side sparse-support query made by one LHS row. -/
noncomputable def lhsSupportRowCheck
    (groupCount signatureCount memberEnc labelEnc groupEnc locationCs locationPmask : ℕ)
    (locationTree : Lean.RArray ℕ) (left : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis right ↦
      Bool.rec false (inductionHypothesis right.succ)
        (lhsSupportPairCheck signatureCount memberEnc labelEnc groupEnc locationCs locationPmask
          locationTree left right))
    (Nat.sub groupCount left) left

/-- Sign bit of a packed signed natural. -/
noncomputable def signedSign (value : ℕ) : ℕ := Nat.land value 1

/-- Magnitude of a packed signed natural. -/
noncomputable def signedMagnitude (value : ℕ) : ℕ := Nat.shiftRight value 1

/-- Normalize two nonnegative lanes and pack the resulting signed natural. -/
noncomputable def signedEncode (positive negative : ℕ) : ℕ :=
  Bool.rec
    (Nat.add (Nat.shiftLeft (Nat.sub negative positive) 1) 1)
    (Nat.shiftLeft (Nat.sub positive negative) 1)
    (Nat.ble negative positive)

/-- High moment lane of one unordered signature pair. -/
noncomputable def lhsMomentTop (pairCs pairPmask pairWidth pairMask outWidth : ℕ)
    (pairTree : Lean.RArray ℕ) (left right : ℕ) : ℕ :=
  Nat.shiftRight
    (treeAt pairCs pairPmask pairWidth pairMask pairTree (triIdx left right)) outWidth

/-- Direct signed moment transform of one LHS group at one target signature. -/
noncomputable def lhsTransformValue
    (memberEnc labelEnc groupEnc coefficientCs coefficientPmask coefficientWidth
      coefficientMask pairCs pairPmask pairWidth pairMask outWidth : ℕ)
    (coefficientTree pairTree : Lean.RArray ℕ) (group target : ℕ) : ℕ :=
  let groupField := groupField groupEnc group
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ)
    (fun _ positive negative ↦ signedEncode positive negative)
    (fun _ inductionHypothesis cursor positive negative ↦
      let label := lhsMember memberEnc cursor
      let labelField := labelField labelEnc label
      let magnitude := treeAt coefficientCs coefficientPmask coefficientWidth coefficientMask
        coefficientTree label
      let term := Nat.mul magnitude (lhsMomentTop pairCs pairPmask pairWidth pairMask outWidth
        pairTree target (labelSignature labelField))
      Bool.rec
        (inductionHypothesis cursor.succ positive (Nat.add negative term))
        (inductionHypothesis cursor.succ (Nat.add positive term) negative)
        (Nat.beq (labelSign labelField) 0))
    (groupSize groupField) (groupStart groupField) 0 0

/-- Check a consecutive range of stored sparse LHS transform entries. -/
noncomputable def lhsTransformCheck
    (transformCs transformPmask transformWidth transformMask memberEnc labelEnc groupEnc keyEnc
      coefficientCs coefficientPmask coefficientWidth coefficientMask pairCs pairPmask pairWidth
      pairMask outWidth : ℕ)
    (transformTree coefficientTree pairTree : Lean.RArray ℕ) (lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis entry ↦
      let key := keyField keyEnc entry
      Bool.rec false (inductionHypothesis entry.succ)
        (Nat.beq (treeAt transformCs transformPmask transformWidth transformMask
          transformTree entry)
          (lhsTransformValue memberEnc labelEnc groupEnc coefficientCs coefficientPmask
            coefficientWidth coefficientMask pairCs pairPmask pairWidth pairMask outWidth
            coefficientTree pairTree (keyGroup key) (keyTarget key))))
    (Nat.sub upper lower) lower

/-- Stored signed transform value for a group and target, through a one-based location table. -/
noncomputable def lhsTransformAt
    (signatureCount locationCs locationPmask transformCs transformPmask transformWidth
      transformMask : ℕ) (locationTree transformTree : Lean.RArray ℕ)
    (group target : ℕ) : ℕ :=
  let location := treeAt locationCs locationPmask 16 65535 locationTree
    (Nat.add (Nat.mul group signatureCount) target)
  treeAt transformCs transformPmask transformWidth transformMask transformTree (Nat.sub location 1)

/-- Sparse contraction between two LHS degree groups. -/
noncomputable def lhsContractionValue
    (signatureCount memberEnc labelEnc groupEnc locationCs locationPmask transformCs
      transformPmask transformWidth transformMask coefficientCs coefficientPmask coefficientWidth
      coefficientMask : ℕ)
    (locationTree transformTree coefficientTree : Lean.RArray ℕ) (left right : ℕ) : ℕ :=
  let leftField := groupField groupEnc left
  let rightField := groupField groupEnc right
  let useLeft := Nat.ble (groupSize leftField) (groupSize rightField)
  let sourceField := Bool.rec rightField leftField useLeft
  let transformGroup := Bool.rec left right useLeft
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ)
    (fun _ positive negative ↦ signedEncode positive negative)
    (fun _ inductionHypothesis cursor positive negative ↦
      let label := lhsMember memberEnc cursor
      let labelField := labelField labelEnc label
      let coefficient := treeAt coefficientCs coefficientPmask coefficientWidth coefficientMask
        coefficientTree label
      let transform := lhsTransformAt signatureCount locationCs locationPmask transformCs
        transformPmask transformWidth transformMask locationTree transformTree transformGroup
        (labelSignature labelField)
      let term := Nat.mul coefficient (signedMagnitude transform)
      Bool.rec
        (inductionHypothesis cursor.succ positive (Nat.add negative term))
        (inductionHypothesis cursor.succ (Nat.add positive term) negative)
        (Nat.beq (labelSign labelField) (signedSign transform)))
    (groupSize sourceField) (groupStart sourceField) 0 0

/-- One signed upper-triangular LHS group row. -/
noncomputable def lhsRowValue
    (groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask coefficientCs coefficientPmask
      coefficientWidth coefficientMask scalarCs scalarPmask scalarWidth scalarMask : ℕ)
    (locationTree transformTree coefficientTree scalarTree : Lean.RArray ℕ) (left : ℕ) : ℕ :=
  let leftField := groupField groupEnc left
  Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ)
    (fun _ positive negative ↦ signedEncode positive negative)
    (fun _ inductionHypothesis right positive negative ↦
      let rightField := groupField groupEnc right
      let contraction := lhsContractionValue signatureCount memberEnc labelEnc groupEnc locationCs
        locationPmask transformCs transformPmask transformWidth transformMask coefficientCs
        coefficientPmask coefficientWidth coefficientMask locationTree transformTree coefficientTree
        left right
      let d := Nat.add (Nat.add (Nat.add (groupLowDegree leftField) (groupLowDegree rightField))
        (groupHighDegree leftField)) (groupHighDegree rightField)
      let aSum := Nat.add (groupLowDegree leftField) (groupLowDegree rightField)
      let scalar := treeAt scalarCs scalarPmask scalarWidth scalarMask scalarTree
        (Nat.add (Nat.mul d scalarDimension) aSum)
      let factor := Bool.rec scalar (Nat.mul 2 scalar) (Nat.blt left right)
      let term := Nat.mul factor (signedMagnitude contraction)
      Bool.rec
        (inductionHypothesis right.succ positive (Nat.add negative term))
        (inductionHypothesis right.succ (Nat.add positive term) negative)
        (Nat.beq (signedSign contraction) 0))
    (Nat.sub groupCount left) left 0 0

/-- Check a consecutive range of final sparse LHS rows. -/
noncomputable def lhsRowCheck
    (groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth rowMask
      coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
      scalarWidth scalarMask : ℕ)
    (locationTree transformTree rowTree coefficientTree scalarTree : Lean.RArray ℕ)
    (lower upper : ℕ) : Bool :=
  Nat.rec (motive := fun _ ↦ ℕ → Bool)
    (fun _ ↦ true)
    (fun _ inductionHypothesis left ↦
      Bool.rec false (inductionHypothesis left.succ)
        ((Nat.beq (treeAt rowCs rowPmask rowWidth rowMask rowTree left)
            (lhsRowValue groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc
              locationCs locationPmask transformCs transformPmask transformWidth transformMask
              coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
              scalarWidth scalarMask locationTree transformTree coefficientTree scalarTree left))
          && (lhsSupportRowCheck groupCount signatureCount memberEnc labelEnc groupEnc locationCs
            locationPmask locationTree left)))
    (Nat.sub upper lower) lower

end cert246Data
