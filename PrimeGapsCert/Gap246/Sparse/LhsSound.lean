/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.LHSScalar
public import PrimeGapsCert.Gap246.Sparse.AccessorBridge
public import PrimeGapsCert.Gap246.Sparse.SignedSound

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

/-! # Soundness of the first-order sparse LHS kernel -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Integer coefficient represented by one position of the flattened LHS permutation. -/
noncomputable def lhsLabelValue
    (memberEnc labelEnc coefficientCs coefficientPmask coefficientWidth coefficientMask : ℕ)
    (coefficientTree : Lean.RArray ℕ) (position : ℕ) : ℤ :=
  let label := cert246Data.lhsMember memberEnc position
  let labelField := cert246Data.labelField labelEnc label
  let magnitude := cert246Data.treeAt coefficientCs coefficientPmask coefficientWidth
    coefficientMask coefficientTree label
  if cert246Data.labelSign labelField = 0 then magnitude else -magnitude

/-- Mathematical integer sum represented by one raw LHS transform. -/
noncomputable def lhsTransformSpec
    (memberEnc labelEnc groupEnc coefficientCs coefficientPmask coefficientWidth coefficientMask
      pairCs pairPmask pairWidth pairMask outWidth : ℕ)
    (coefficientTree pairTree : Lean.RArray ℕ) (group target : ℕ) : ℤ :=
  let groupField := cert246Data.groupField groupEnc group
  ∑ offset ∈ Finset.range (cert246Data.groupSize groupField),
    lhsLabelValue memberEnc labelEnc coefficientCs coefficientPmask coefficientWidth
        coefficientMask coefficientTree (cert246Data.groupStart groupField + offset) *
      cert246Data.lhsMomentTop pairCs pairPmask pairWidth pairMask outWidth pairTree target
        (cert246Data.labelSignature (cert246Data.labelField labelEnc
          (cert246Data.lhsMember memberEnc
            (cert246Data.groupStart groupField + offset))))

/-- The raw two-lane LHS transform denotes its integer finite sum. -/
theorem lhsTransformValue_sound
    (memberEnc labelEnc groupEnc coefficientCs coefficientPmask coefficientWidth coefficientMask
      pairCs pairPmask pairWidth pairMask outWidth : ℕ)
    (coefficientTree pairTree : Lean.RArray ℕ) (group target : ℕ) :
    signedValue
        (cert246Data.lhsTransformValue memberEnc labelEnc groupEnc coefficientCs
          coefficientPmask coefficientWidth coefficientMask pairCs pairPmask pairWidth pairMask
          outWidth coefficientTree pairTree group target) =
      lhsTransformSpec memberEnc labelEnc groupEnc coefficientCs coefficientPmask coefficientWidth
        coefficientMask pairCs pairPmask pairWidth pairMask outWidth coefficientTree pairTree group
        target := by
  unfold cert246Data.lhsTransformValue lhsTransformSpec
  let groupField := cert246Data.groupField groupEnc group
  let positive : ℕ → Bool := fun cursor ↦
    Nat.beq (cert246Data.labelSign
      (cert246Data.labelField labelEnc (cert246Data.lhsMember memberEnc cursor))) 0
  let term : ℕ → ℕ := fun cursor ↦
    cert246Data.treeAt coefficientCs coefficientPmask coefficientWidth coefficientMask
        coefficientTree (cert246Data.lhsMember memberEnc cursor) *
      cert246Data.lhsMomentTop pairCs pairPmask pairWidth pairMask outWidth pairTree target
        (cert246Data.labelSignature
          (cert246Data.labelField labelEnc (cert246Data.lhsMember memberEnc cursor)))
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [signedRec_sound positive term]
  simp only [Int.ofNat_zero, sub_self, zero_add]
  apply Finset.sum_congr rfl
  intro offset _
  unfold positive term lhsLabelValue
  simp only [Nat.beq_eq]
  split <;> push_cast <;> ring

/-- A successful raw transform-range check yields every stored equality in that range. -/
theorem lhsTransformCheck_sound
    {transformCs transformPmask transformWidth transformMask memberEnc labelEnc groupEnc keyEnc
      coefficientCs coefficientPmask coefficientWidth coefficientMask pairCs pairPmask pairWidth
      pairMask outWidth lower upper : ℕ}
    {transformTree coefficientTree pairTree : Lean.RArray ℕ}
    (hcheck : cert246Data.lhsTransformCheck transformCs transformPmask transformWidth
      transformMask memberEnc labelEnc groupEnc keyEnc coefficientCs coefficientPmask
      coefficientWidth coefficientMask pairCs pairPmask pairWidth pairMask outWidth transformTree
      coefficientTree pairTree lower upper = true) :
    ∀ entry, lower ≤ entry → entry < upper →
      cert246Data.treeAt transformCs transformPmask transformWidth transformMask transformTree
          entry =
        let key := cert246Data.keyField keyEnc entry
        cert246Data.lhsTransformValue memberEnc labelEnc groupEnc coefficientCs coefficientPmask
          coefficientWidth coefficientMask pairCs pairPmask pairWidth pairMask outWidth
          coefficientTree pairTree (cert246Data.keyGroup key)
          (cert246Data.keyTarget key) := by
  intro entry hlower hupper
  unfold cert246Data.lhsTransformCheck at hcheck
  have hentry := boolRec_sound
    (fun entry ↦
      let key := cert246Data.keyField keyEnc entry
      Nat.beq
        (cert246Data.treeAt transformCs transformPmask transformWidth transformMask
          transformTree entry)
        (cert246Data.lhsTransformValue memberEnc labelEnc groupEnc coefficientCs
          coefficientPmask coefficientWidth coefficientMask pairCs pairPmask pairWidth pairMask
          outWidth coefficientTree pairTree (cert246Data.keyGroup key)
          (cert246Data.keyTarget key)))
    (upper - lower) lower hcheck entry hlower (by omega)
  simpa only [Nat.beq_eq] using hentry

/-- A successful ranged packed-key check bounds every entry in that range. -/
theorem lhsKeysRangeCheck_sound
    {groupCount signatureCount keyEnc lower upper : ℕ}
    (hcheck : cert246Data.lhsKeysRangeCheck groupCount signatureCount keyEnc lower upper = true) :
    ∀ entry, lower ≤ entry → entry < upper →
      let field := cert246Data.keyField keyEnc entry
      cert246Data.keyGroup field < groupCount ∧
        cert246Data.keyTarget field < signatureCount := by
  intro entry hlower hupper
  unfold cert246Data.lhsKeysRangeCheck at hcheck
  have h := boolRec_sound
    (fun entry ↦
      let field := cert246Data.keyField keyEnc entry
      Bool.and' (Nat.blt (cert246Data.keyGroup field) groupCount)
        (Nat.blt (cert246Data.keyTarget field) signatureCount))
    (upper - lower) lower hcheck entry (by omega) (by omega)
  simpa only [Bool.and'_eq_and, Bool.and_eq_true, Nat.blt_eq] using h

/-- A successful ranged sparse-location check decodes every group row in that range. -/
theorem lhsLocationIndexRangeCheck_sound
    {signatureCount entryCount locationCs locationPmask keyEnc lower upper : ℕ}
    {locationTree : Lean.RArray ℕ}
    (hcheck : cert246Data.lhsLocationIndexRangeCheck signatureCount entryCount
      locationCs locationPmask keyEnc locationTree lower upper = true) :
    ∀ group, lower ≤ group → group < upper → ∀ target < signatureCount,
      let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (group * signatureCount + target)
      location = 0 ∨
        (0 < location ∧ location ≤ entryCount ∧
          cert246Data.keyGroup
              (cert246Data.keyField keyEnc (location - 1)) = group ∧
            cert246Data.keyTarget
              (cert246Data.keyField keyEnc (location - 1)) = target) := by
  intro group hlower hupper target htarget
  unfold cert246Data.lhsLocationIndexRangeCheck at hcheck
  have hgroupCheck := boolRec_sound
    (fun group ↦
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
        (fun _ ↦ true)
        (fun _ targetHypothesis target ↦
          let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
            (group * signatureCount + target)
          let key := cert246Data.keyField keyEnc (location - 1)
          let valid := Bool.rec
            (Bool.and' (Nat.ble location entryCount)
              (Bool.and' (Nat.beq (cert246Data.keyGroup key) group)
                (Nat.beq (cert246Data.keyTarget key) target)))
            true (Nat.beq location 0)
          Bool.rec false (targetHypothesis target.succ) valid)
        signatureCount 0)
    (upper - lower) lower hcheck group (by omega) (by omega)
  have hentry := boolRec_sound
    (fun target ↦
      let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (group * signatureCount + target)
      let key := cert246Data.keyField keyEnc (location - 1)
      Bool.rec
        (Bool.and' (Nat.ble location entryCount)
          (Bool.and' (Nat.beq (cert246Data.keyGroup key) group)
            (Nat.beq (cert246Data.keyTarget key) target)))
        true (Nat.beq location 0))
    signatureCount 0 hgroupCheck target (by omega) (by omega)
  let location := cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
    (group * signatureCount + target)
  by_cases hzero : location = 0
  · exact Or.inl hzero
  · have hfalse : Nat.beq location 0 = false :=
      Bool.eq_false_of_not_eq_true fun h ↦ hzero (Nat.beq_eq.mp h)
    change Bool.rec
      (Bool.and' (Nat.ble location entryCount)
        (Bool.and' (Nat.beq (cert246Data.keyGroup
            (cert246Data.keyField keyEnc (location - 1))) group)
          (Nat.beq (cert246Data.keyTarget
            (cert246Data.keyField keyEnc (location - 1))) target)))
      true (Nat.beq location 0) = true at hentry
    rw [hfalse] at hentry
    exact Or.inr ⟨Nat.pos_of_ne_zero hzero, by
      simpa only [Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq] using hentry⟩

/-- A successful pair-support check makes every smaller-side transform location positive. -/
theorem lhsSupportPairCheck_sound
    {signatureCount memberEnc labelEnc groupEnc locationCs locationPmask left right : ℕ}
    {locationTree : Lean.RArray ℕ}
    (hcheck : cert246Data.lhsSupportPairCheck signatureCount memberEnc labelEnc groupEnc
      locationCs locationPmask locationTree left right = true) :
    let leftField := cert246Data.groupField groupEnc left
    let rightField := cert246Data.groupField groupEnc right
    let useLeft := Nat.ble (cert246Data.groupSize leftField)
      (cert246Data.groupSize rightField)
    let sourceField : ℕ := Bool.rec rightField leftField useLeft
    let transformGroup : ℕ := Bool.rec left right useLeft
    ∀ offset < cert246Data.groupSize sourceField,
      let label := cert246Data.lhsMember memberEnc
        (cert246Data.groupStart sourceField + offset)
      let target := cert246Data.labelSignature (cert246Data.labelField labelEnc label)
      0 < cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (transformGroup * signatureCount + target) := by
  dsimp only
  intro offset hoffset
  let leftField := cert246Data.groupField groupEnc left
  let rightField := cert246Data.groupField groupEnc right
  let useLeft := Nat.ble (cert246Data.groupSize leftField)
    (cert246Data.groupSize rightField)
  let sourceField : ℕ := Bool.rec rightField leftField useLeft
  let transformGroup : ℕ := Bool.rec left right useLeft
  have hoffset' : offset < cert246Data.groupSize sourceField := by
    simpa only [leftField, rightField, useLeft, sourceField] using hoffset
  have hscan :
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
          (fun _ ↦ true)
          (fun _ inductionHypothesis cursor ↦
            let label := cert246Data.lhsMember memberEnc cursor
            let target := cert246Data.labelSignature (cert246Data.labelField labelEnc label)
            Bool.rec false (inductionHypothesis cursor.succ)
              (Nat.blt 0 (cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
                (transformGroup * signatureCount + target))))
          (cert246Data.groupSize sourceField)
          (cert246Data.groupStart sourceField) = true := by
    simpa only [cert246Data.lhsSupportPairCheck, leftField, rightField, useLeft,
      sourceField, transformGroup, Nat.add_eq, Nat.mul_eq, Nat.sub_eq] using hcheck
  have h := boolRec_sound
    (fun cursor ↦
      let label := cert246Data.lhsMember memberEnc cursor
      let target := cert246Data.labelSignature (cert246Data.labelField labelEnc label)
      Nat.blt 0 (cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
        (transformGroup * signatureCount + target)))
    (cert246Data.groupSize sourceField)
    (cert246Data.groupStart sourceField) hscan
    (cert246Data.groupStart sourceField + offset)
    (by omega) (by omega)
  simpa only [Nat.blt_eq, leftField, rightField, useLeft, sourceField,
    transformGroup] using h

/-- A successful row-support check covers every contraction query in that upper row. -/
theorem lhsSupportRowCheck_sound
    {groupCount signatureCount memberEnc labelEnc groupEnc locationCs locationPmask : ℕ}
    {locationTree : Lean.RArray ℕ} {left : ℕ}
    (hcheck : cert246Data.lhsSupportRowCheck groupCount signatureCount memberEnc labelEnc groupEnc
      locationCs locationPmask locationTree left = true) :
    ∀ right, left ≤ right → right < groupCount →
      let leftField := cert246Data.groupField groupEnc left
      let rightField := cert246Data.groupField groupEnc right
      let useLeft := Nat.ble (cert246Data.groupSize leftField)
        (cert246Data.groupSize rightField)
      let sourceField : ℕ := Bool.rec rightField leftField useLeft
      let transformGroup : ℕ := Bool.rec left right useLeft
      ∀ offset < cert246Data.groupSize sourceField,
        let label := cert246Data.lhsMember memberEnc
          (cert246Data.groupStart sourceField + offset)
        let target := cert246Data.labelSignature (cert246Data.labelField labelEnc label)
        0 < cert246Data.treeAt locationCs locationPmask 16 65535 locationTree
          (transformGroup * signatureCount + target) := by
  intro right hright hrightBound
  unfold cert246Data.lhsSupportRowCheck at hcheck
  have hpair := boolRec_sound
    (fun right ↦ cert246Data.lhsSupportPairCheck signatureCount memberEnc labelEnc groupEnc
      locationCs locationPmask locationTree left right)
    (groupCount - left) left hcheck right hright (by omega)
  exact lhsSupportPairCheck_sound hpair

/-- A successful scalar-row check identifies every entry in that row. -/
theorem lhsScalarRowCheck_sound
    {dimension epsilonDenominator degreeBound scalarDimension scalarCs scalarPmask scalarWidth
      scalarMask d : ℕ} {scalarTree : Lean.RArray ℕ}
    (hcheck : cert246Data.lhsScalarRowCheck dimension epsilonDenominator degreeBound
      scalarDimension scalarCs scalarPmask scalarWidth scalarMask scalarTree d = true) :
    d ≤ dimension → ∀ aSum < scalarDimension, aSum ≤ d →
      cert246Data.treeAt scalarCs scalarPmask scalarWidth scalarMask scalarTree
          (d * scalarDimension + aSum) =
        cert246Data.lhsScalarFormula dimension epsilonDenominator degreeBound d aSum := by
  intro hd aSum ha haD
  unfold cert246Data.lhsScalarRowCheck at hcheck
  have h := boolRec_sound
    (fun aSum ↦ Nat.beq
      (cert246Data.treeAt scalarCs scalarPmask scalarWidth scalarMask scalarTree
        (d * scalarDimension + aSum))
      (Bool.rec 0 (cert246Data.lhsScalarFormula dimension epsilonDenominator degreeBound d aSum)
        (Bool.and' (Nat.ble d dimension) (Nat.ble aSum d))))
    scalarDimension 0 hcheck aSum (by omega) (by omega)
  have hvalid : Bool.and' (Nat.ble d dimension) (Nat.ble aSum d) = true := by
    simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.ble_eq]
    exact ⟨hd, haD⟩
  rw [hvalid] at h
  simpa only [Nat.beq_eq] using h

private theorem lhsLabelProductTerm
    (memberEnc labelEnc coefficientCs coefficientPmask coefficientWidth coefficientMask : ℕ)
    (coefficientTree : Lean.RArray ℕ) (position transform : ℕ) :
    let label := cert246Data.lhsMember memberEnc position
    let labelField := cert246Data.labelField labelEnc label
    let magnitude := cert246Data.treeAt coefficientCs coefficientPmask coefficientWidth
      coefficientMask coefficientTree label
    (if cert246Data.labelSign labelField = cert246Data.signedSign transform then
        (magnitude * cert246Data.signedMagnitude transform : ℤ)
      else -(magnitude * cert246Data.signedMagnitude transform : ℤ)) =
      lhsLabelValue memberEnc labelEnc coefficientCs coefficientPmask coefficientWidth
        coefficientMask coefficientTree position * signedValue transform := by
  dsimp only
  have hlabel := labelSign_lt_two (cert246Data.labelField labelEnc
    (cert246Data.lhsMember memberEnc position))
  have htransform := signedSign_lt_two transform
  interval_cases hlabelSign : cert246Data.labelSign
      (cert246Data.labelField labelEnc (cert246Data.lhsMember memberEnc position)) <;>
    interval_cases htransformSign : cert246Data.signedSign transform <;>
      simp [lhsLabelValue, signedValue, hlabelSign, htransformSign]

/-- Mathematical integer sum represented by one raw LHS group contraction. -/
noncomputable def lhsContractionSpec
    (signatureCount memberEnc labelEnc groupEnc locationCs locationPmask transformCs
      transformPmask transformWidth transformMask coefficientCs coefficientPmask coefficientWidth
      coefficientMask : ℕ)
    (locationTree transformTree coefficientTree : Lean.RArray ℕ) (left right : ℕ) : ℤ :=
  let leftField := cert246Data.groupField groupEnc left
  let rightField := cert246Data.groupField groupEnc right
  let useLeft := Nat.ble (cert246Data.groupSize leftField)
    (cert246Data.groupSize rightField)
  let sourceField : ℕ := Bool.rec rightField leftField useLeft
  let transformGroup : ℕ := Bool.rec left right useLeft
  ∑ offset ∈ Finset.range (cert246Data.groupSize sourceField),
    let position := cert246Data.groupStart sourceField + offset
    let label := cert246Data.lhsMember memberEnc position
    let labelField := cert246Data.labelField labelEnc label
    lhsLabelValue memberEnc labelEnc coefficientCs coefficientPmask coefficientWidth
        coefficientMask coefficientTree position *
      signedValue (cert246Data.lhsTransformAt signatureCount locationCs locationPmask transformCs
        transformPmask transformWidth transformMask locationTree transformTree transformGroup
        (cert246Data.labelSignature labelField))

/-- The raw two-lane LHS contraction denotes its integer finite sum. -/
theorem lhsContractionValue_sound
    (signatureCount memberEnc labelEnc groupEnc locationCs locationPmask transformCs
      transformPmask transformWidth transformMask coefficientCs coefficientPmask coefficientWidth
      coefficientMask : ℕ)
    (locationTree transformTree coefficientTree : Lean.RArray ℕ) (left right : ℕ) :
    signedValue
        (cert246Data.lhsContractionValue signatureCount memberEnc labelEnc groupEnc locationCs
          locationPmask transformCs transformPmask transformWidth transformMask coefficientCs
          coefficientPmask coefficientWidth coefficientMask locationTree transformTree
          coefficientTree left right) =
      lhsContractionSpec signatureCount memberEnc labelEnc groupEnc locationCs locationPmask
        transformCs transformPmask transformWidth transformMask coefficientCs coefficientPmask
        coefficientWidth coefficientMask locationTree transformTree coefficientTree left right := by
  unfold cert246Data.lhsContractionValue lhsContractionSpec
  let leftField := cert246Data.groupField groupEnc left
  let rightField := cert246Data.groupField groupEnc right
  let useLeft := Nat.ble (cert246Data.groupSize leftField)
    (cert246Data.groupSize rightField)
  let sourceField : ℕ := Bool.rec rightField leftField useLeft
  let transformGroup : ℕ := Bool.rec left right useLeft
  let transform : ℕ → ℕ := fun cursor ↦
    let label := cert246Data.lhsMember memberEnc cursor
    cert246Data.lhsTransformAt signatureCount locationCs locationPmask transformCs
      transformPmask transformWidth transformMask locationTree transformTree transformGroup
      (cert246Data.labelSignature (cert246Data.labelField labelEnc label))
  let positive : ℕ → Bool := fun cursor ↦
    Nat.beq
      (cert246Data.labelSign
        (cert246Data.labelField labelEnc (cert246Data.lhsMember memberEnc cursor)))
      (cert246Data.signedSign (transform cursor))
  let term : ℕ → ℕ := fun cursor ↦
    cert246Data.treeAt coefficientCs coefficientPmask coefficientWidth coefficientMask
        coefficientTree (cert246Data.lhsMember memberEnc cursor) *
      cert246Data.signedMagnitude (transform cursor)
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [signedRec_sound positive term]
  simp only [Int.ofNat_zero, sub_self, zero_add]
  apply Finset.sum_congr rfl
  intro offset _
  unfold positive term transform
  simp only [Nat.beq_eq]
  exact lhsLabelProductTerm memberEnc labelEnc coefficientCs coefficientPmask coefficientWidth
    coefficientMask coefficientTree (cert246Data.groupStart sourceField + offset) _

/-- Mathematical integer sum represented by one raw LHS row. -/
noncomputable def lhsRowSpec
    (groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask coefficientCs coefficientPmask
      coefficientWidth coefficientMask scalarCs scalarPmask scalarWidth scalarMask : ℕ)
    (locationTree transformTree coefficientTree scalarTree : Lean.RArray ℕ)
    (left : ℕ) : ℤ :=
  let leftField := cert246Data.groupField groupEnc left
  ∑ offset ∈ Finset.range (groupCount - left),
    let right := left + offset
    let rightField := cert246Data.groupField groupEnc right
    let d := cert246Data.groupLowDegree leftField + cert246Data.groupLowDegree rightField +
      cert246Data.groupHighDegree leftField + cert246Data.groupHighDegree rightField
    let aSum := cert246Data.groupLowDegree leftField + cert246Data.groupLowDegree rightField
    let scalar := cert246Data.treeAt scalarCs scalarPmask scalarWidth scalarMask scalarTree
      (d * scalarDimension + aSum)
    let factor := Bool.rec scalar (2 * scalar) (Nat.blt left right)
    factor * lhsContractionSpec signatureCount memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask coefficientCs coefficientPmask
      coefficientWidth coefficientMask locationTree transformTree coefficientTree left right

/-- The raw two-lane LHS row denotes its integer finite sum. -/
theorem lhsRowValue_sound
    (groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask coefficientCs coefficientPmask
      coefficientWidth coefficientMask scalarCs scalarPmask scalarWidth scalarMask : ℕ)
    (locationTree transformTree coefficientTree scalarTree : Lean.RArray ℕ) (left : ℕ) :
    signedValue
        (cert246Data.lhsRowValue groupCount signatureCount scalarDimension memberEnc labelEnc
          groupEnc locationCs locationPmask transformCs transformPmask transformWidth transformMask
          coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
          scalarWidth scalarMask locationTree transformTree coefficientTree scalarTree left) =
      lhsRowSpec groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs
        locationPmask transformCs transformPmask transformWidth transformMask coefficientCs
        coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask scalarWidth
        scalarMask locationTree transformTree coefficientTree scalarTree left := by
  unfold cert246Data.lhsRowValue lhsRowSpec
  let leftField := cert246Data.groupField groupEnc left
  let contraction : ℕ → ℕ := fun right ↦
    cert246Data.lhsContractionValue signatureCount memberEnc labelEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask coefficientCs
      coefficientPmask coefficientWidth coefficientMask locationTree transformTree coefficientTree
      left right
  let factor : ℕ → ℕ := fun right ↦
    let rightField := cert246Data.groupField groupEnc right
    let d := cert246Data.groupLowDegree leftField + cert246Data.groupLowDegree rightField +
      cert246Data.groupHighDegree leftField + cert246Data.groupHighDegree rightField
    let aSum := cert246Data.groupLowDegree leftField + cert246Data.groupLowDegree rightField
    let scalar := cert246Data.treeAt scalarCs scalarPmask scalarWidth scalarMask scalarTree
      (d * scalarDimension + aSum)
    Bool.rec scalar (2 * scalar) (Nat.blt left right)
  let positive : ℕ → Bool := fun right ↦
    Nat.beq (cert246Data.signedSign (contraction right)) 0
  let term : ℕ → ℕ := fun right ↦
    factor right * cert246Data.signedMagnitude (contraction right)
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  rw [signedRec_sound positive term]
  simp only [Int.ofNat_zero, sub_self, zero_add]
  apply Finset.sum_congr rfl
  intro offset _
  unfold positive term
  simp only [Nat.beq_eq]
  let value := contraction (left + offset)
  have hterm :
      (if cert246Data.signedSign value = 0 then
          ((factor (left + offset) * cert246Data.signedMagnitude value : ℕ) : ℤ)
        else -((factor (left + offset) * cert246Data.signedMagnitude value : ℕ) : ℤ)) =
        Int.ofNat (factor (left + offset)) * signedValue value :=
    calc
      _ = if cert246Data.signedSign value = 0 then
            ((cert246Data.signedMagnitude value * factor (left + offset) : ℕ) : ℤ)
          else
            -((cert246Data.signedMagnitude value * factor (left + offset) : ℕ) : ℤ) := by
        split <;> rw [Nat.mul_comm]
      _ = signedValue value * Int.ofNat (factor (left + offset)) :=
        signedScaleTermNat value (factor (left + offset))
      _ = _ := by ring
  rw [hterm]
  have hcontraction := lhsContractionValue_sound signatureCount memberEnc labelEnc groupEnc
    locationCs locationPmask transformCs transformPmask transformWidth transformMask coefficientCs
    coefficientPmask coefficientWidth coefficientMask locationTree transformTree coefficientTree
    left (left + offset)
  change signedValue value = _ at hcontraction
  rw [hcontraction]
  unfold factor
  rcases hfactor : Nat.blt left (left + offset) with _ | _ <;> norm_num [leftField]

private theorem lhsRowCheck_entry
    {groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth rowMask
      coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
      scalarWidth scalarMask lower upper : ℕ}
    {locationTree transformTree rowTree coefficientTree scalarTree : Lean.RArray ℕ}
    (hcheck : cert246Data.lhsRowCheck groupCount signatureCount scalarDimension memberEnc
      labelEnc groupEnc locationCs locationPmask transformCs transformPmask transformWidth
      transformMask rowCs rowPmask rowWidth rowMask coefficientCs coefficientPmask coefficientWidth
      coefficientMask scalarCs scalarPmask scalarWidth scalarMask locationTree transformTree rowTree
      coefficientTree scalarTree lower upper = true) :
    ∀ left, lower ≤ left → left < upper →
      ((Nat.beq (cert246Data.treeAt rowCs rowPmask rowWidth rowMask rowTree left)
            (cert246Data.lhsRowValue groupCount signatureCount scalarDimension memberEnc labelEnc
              groupEnc locationCs locationPmask transformCs transformPmask transformWidth
              transformMask coefficientCs coefficientPmask coefficientWidth coefficientMask
              scalarCs scalarPmask scalarWidth scalarMask locationTree transformTree coefficientTree
              scalarTree left))
          && (cert246Data.lhsSupportRowCheck groupCount signatureCount memberEnc labelEnc groupEnc
            locationCs locationPmask locationTree left)) = true := by
  intro left hlower hupper
  unfold cert246Data.lhsRowCheck at hcheck
  exact boolRec_sound
    (fun left ↦ (Nat.beq (cert246Data.treeAt rowCs rowPmask rowWidth rowMask rowTree left)
        (cert246Data.lhsRowValue groupCount signatureCount scalarDimension memberEnc labelEnc
          groupEnc locationCs locationPmask transformCs transformPmask transformWidth transformMask
          coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
          scalarWidth scalarMask locationTree transformTree coefficientTree scalarTree left))
      && (cert246Data.lhsSupportRowCheck groupCount signatureCount memberEnc labelEnc groupEnc
        locationCs locationPmask locationTree left))
    (upper - lower) lower hcheck left hlower (by omega)

/-- A successful raw row-range check yields every stored equality in that range. -/
theorem lhsRowCheck_sound
    {groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth rowMask
      coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
      scalarWidth scalarMask lower upper : ℕ}
    {locationTree transformTree rowTree coefficientTree scalarTree : Lean.RArray ℕ}
    (hcheck : cert246Data.lhsRowCheck groupCount signatureCount scalarDimension memberEnc
      labelEnc groupEnc locationCs locationPmask transformCs transformPmask transformWidth
      transformMask rowCs rowPmask rowWidth rowMask coefficientCs coefficientPmask coefficientWidth
      coefficientMask scalarCs scalarPmask scalarWidth scalarMask locationTree transformTree rowTree
      coefficientTree scalarTree lower upper = true) :
    ∀ left, lower ≤ left → left < upper →
      cert246Data.treeAt rowCs rowPmask rowWidth rowMask rowTree left =
        cert246Data.lhsRowValue groupCount signatureCount scalarDimension memberEnc labelEnc
          groupEnc locationCs locationPmask transformCs transformPmask transformWidth transformMask
          coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
          scalarWidth scalarMask locationTree transformTree coefficientTree scalarTree left :=
  fun left hlower hupper ↦
    Nat.beq_eq.mp (Bool.and_eq_true_iff.mp (lhsRowCheck_entry hcheck left hlower hupper)).1

/-- A successful raw row-range check also validates every sparse query made by those rows. -/
theorem lhsRowCheck_support_sound
    {groupCount signatureCount scalarDimension memberEnc labelEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth rowMask
      coefficientCs coefficientPmask coefficientWidth coefficientMask scalarCs scalarPmask
      scalarWidth scalarMask lower upper : ℕ}
    {locationTree transformTree rowTree coefficientTree scalarTree : Lean.RArray ℕ}
    (hcheck : cert246Data.lhsRowCheck groupCount signatureCount scalarDimension memberEnc
      labelEnc groupEnc locationCs locationPmask transformCs transformPmask transformWidth
      transformMask rowCs rowPmask rowWidth rowMask coefficientCs coefficientPmask coefficientWidth
      coefficientMask scalarCs scalarPmask scalarWidth scalarMask locationTree transformTree rowTree
      coefficientTree scalarTree lower upper = true) :
    ∀ left, lower ≤ left → left < upper →
      cert246Data.lhsSupportRowCheck groupCount signatureCount memberEnc labelEnc groupEnc
        locationCs locationPmask locationTree left = true := fun left hlower hupper ↦
  (Bool.and_eq_true_iff.mp (lhsRowCheck_entry hcheck left hlower hupper)).2

end PrimeGaps.Gap246
