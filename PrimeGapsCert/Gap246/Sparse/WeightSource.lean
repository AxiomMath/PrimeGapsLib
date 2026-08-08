/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.WeightBase


/-! # Source-fold soundness for packed RHS weights -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

private theorem rhsSourceWeightExponentLanes_sound (laneWidth label : ℕ) :
    ∀ count cursor lanes,
      let result := cert246Data.rhsSourceWeightExponentLanes certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.labelEnc cert246Data.rhsSourceLocationT
        cert246Data.coeffMag label (certRhsSignatureField label) count cursor lanes
      result.bound = lanes.bound + (∑ offset ∈ Finset.range count,
            if certRhsActive label (cursor + offset) = true then
              certRhsMagnitude label (cursor + offset) else 0) ∧
        result.positive = lanes.positive + (∑ offset ∈ Finset.range count,
            if certRhsActive label (cursor + offset) = true ∧ certRhsSign label = 0 then
              Nat.shiftLeft (certRhsMagnitude label (cursor + offset))
                (laneWidth * certRhsSourceLocation label (cursor + offset)) else 0) ∧
        result.negative = lanes.negative + (∑ offset ∈ Finset.range count,
            if certRhsActive label (cursor + offset) = true ∧ certRhsSign label ≠ 0 then
              Nat.shiftLeft (certRhsMagnitude label (cursor + offset))
                (laneWidth * certRhsSourceLocation label (cursor + offset)) else 0) := by
  intro count
  induction count with
  | zero =>
      intro cursor lanes
      simp [cert246Data.rhsSourceWeightExponentLanes]
  | succ count inductionHypothesis =>
      intro cursor lanes
      dsimp only
      rw [sum_range_head (fun exponent ↦
        if certRhsActive label exponent = true then certRhsMagnitude label exponent else 0)
        cursor count]
      rw [sum_range_head (fun exponent ↦
        if certRhsActive label exponent = true ∧ certRhsSign label = 0 then
          Nat.shiftLeft (certRhsMagnitude label exponent)
            (laneWidth * certRhsSourceLocation label exponent) else 0) cursor count]
      rw [sum_range_head (fun exponent ↦
        if certRhsActive label exponent = true ∧ certRhsSign label ≠ 0 then
          Nat.shiftLeft (certRhsMagnitude label exponent)
            (laneWidth * certRhsSourceLocation label exponent) else 0) cursor count]
      simp only [cert246Data.rhsSourceWeightExponentLanes]
      by_cases hactive : certRhsActive label cursor = true
      · have hraw : cert246Data.rhsSignatureHasExponent
            (certRhsSignatureField label) cursor = true := hactive
        rw [hraw]
        norm_num only
        simp only [if_pos True.intro]
        let next := cert246Data.rhsSourceWeightLanesAdd certRhsDegreeBound certRhsSourceCs
          certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
          certRhsCoefficientMask laneWidth cert246Data.labelEnc cert246Data.rhsSourceLocationT
          cert246Data.coeffMag label cursor lanes
        rcases inductionHypothesis cursor.succ next with ⟨hbound, hpositive, hnegative⟩
        rw [hbound, hpositive, hnegative]
        unfold next cert246Data.rhsSourceWeightLanesAdd cert246Data.rhsWeightLanesAdd
        simp only [factorialFold_eq_factorial, descFactorialFold_eq_descFactorial]
        by_cases hsign : certRhsSign label = 0
        · have hsignRaw : cert246Data.labelSign
              (cert246Data.labelField cert246Data.labelEnc label) = 0 := by
            simpa only [certRhsSign, certRhsLabelField] using hsign
          rw [if_pos hsignRaw]
          simp [hactive, hsign, certRhsMagnitude, certRhsSourceLocation, certRhsLabelField]
          omega
        · have hsignRaw : cert246Data.labelSign
              (cert246Data.labelField cert246Data.labelEnc label) ≠ 0 := by
            simpa only [certRhsSign, certRhsLabelField] using hsign
          rw [if_neg hsignRaw]
          simp [hactive, hsign, certRhsMagnitude, certRhsSourceLocation, certRhsLabelField]
          omega
      · have hraw : cert246Data.rhsSignatureHasExponent
            (certRhsSignatureField label) cursor = false := Bool.eq_false_of_not_eq_true hactive
        rw [hraw]
        simp only [Bool.false_eq_true, if_false]
        rcases inductionHypothesis cursor.succ lanes with ⟨hbound, hpositive, hnegative⟩
        rw [hbound, hpositive, hnegative]
        simp [hactive]

private theorem rhsSourceWeightLabelLanes_sound (laneWidth label : ℕ)
    (lanes : cert246Data.RhsWeightLanes) :
    let result := cert246Data.rhsSourceWeightLabelLanes certRhsDegreeBound certRhsSourceCs
      certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
      certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
      cert246Data.rhsSourceLocationT cert246Data.coeffMag label lanes
    result.bound = lanes.bound + (∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
          if certRhsActive label exponent = true then certRhsMagnitude label exponent else 0) ∧
      result.positive = lanes.positive + (∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
          if certRhsActive label exponent = true ∧ certRhsSign label = 0 then
            Nat.shiftLeft (certRhsMagnitude label exponent)
              (laneWidth * certRhsSourceLocation label exponent) else 0) ∧
      result.negative = lanes.negative + (∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
          if certRhsActive label exponent = true ∧ certRhsSign label ≠ 0 then
            Nat.shiftLeft (certRhsMagnitude label exponent)
              (laneWidth * certRhsSourceLocation label exponent) else 0) := by
  unfold cert246Data.rhsSourceWeightLabelLanes
  dsimp only
  simpa only [certRhsSignatureField, certRhsLabelField, Nat.zero_add] using
    rhsSourceWeightExponentLanes_sound laneWidth label (certRhsDegreeBound + 1) 0 lanes

/-- The source-label range fold equals its direct bounded finite sums. -/
theorem rhsSourceWeightLabelRangeLanes_sound (laneWidth : ℕ) :
    ∀ count cursor,
      let result := cert246Data.rhsSourceWeightLabelRangeLanes certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag count cursor
      result.bound = (∑ offset ∈ Finset.range count,
            ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
              if certRhsActive (cursor + offset) exponent = true then
                certRhsMagnitude (cursor + offset) exponent else 0) ∧
        result.positive = (∑ offset ∈ Finset.range count,
            ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
              if certRhsActive (cursor + offset) exponent = true ∧
                  certRhsSign (cursor + offset) = 0 then
                Nat.shiftLeft (certRhsMagnitude (cursor + offset) exponent)
                  (laneWidth * certRhsSourceLocation (cursor + offset) exponent) else 0) ∧
        result.negative = (∑ offset ∈ Finset.range count,
            ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
              if certRhsActive (cursor + offset) exponent = true ∧
                  certRhsSign (cursor + offset) ≠ 0 then
                Nat.shiftLeft (certRhsMagnitude (cursor + offset) exponent)
                  (laneWidth * certRhsSourceLocation (cursor + offset) exponent) else 0) := by
  intro count
  induction count with
  | zero =>
      intro cursor
      simp [cert246Data.rhsSourceWeightLabelRangeLanes]
  | succ count inductionHypothesis =>
      intro cursor
      dsimp only
      rw [sum_range_head (fun label ↦
        ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
          if certRhsActive label exponent = true then certRhsMagnitude label exponent else 0)
        cursor count]
      rw [sum_range_head (fun label ↦
        ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
          if certRhsActive label exponent = true ∧ certRhsSign label = 0 then
            Nat.shiftLeft (certRhsMagnitude label exponent)
              (laneWidth * certRhsSourceLocation label exponent) else 0) cursor count]
      rw [sum_range_head (fun label ↦
        ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
          if certRhsActive label exponent = true ∧ certRhsSign label ≠ 0 then
            Nat.shiftLeft (certRhsMagnitude label exponent)
              (laneWidth * certRhsSourceLocation label exponent) else 0) cursor count]
      simp only [cert246Data.rhsSourceWeightLabelRangeLanes]
      rcases inductionHypothesis cursor.succ with ⟨hbound, hpositive, hnegative⟩
      rcases rhsSourceWeightLabelLanes_sound laneWidth cursor
        (cert246Data.rhsSourceWeightLabelRangeLanes certRhsDegreeBound certRhsSourceCs
          certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
          certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
          cert246Data.rhsSourceLocationT cert246Data.coeffMag count cursor.succ) with
        ⟨hlabelBound, hlabelPositive, hlabelNegative⟩
      constructor
      · rw [hlabelBound, hbound]
        simp only [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
      · constructor
        · rw [hlabelPositive, hpositive]
          simp only [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
        · rw [hlabelNegative, hnegative]
          simp only [Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]

/-- Two weight-lane records are equal when their three natural components are equal. -/
theorem rhsWeightLanes_ext {left right : cert246Data.RhsWeightLanes}
    (hbound : left.bound = right.bound) (hpositive : left.positive = right.positive)
    (hnegative : left.negative = right.negative) : left = right := by
  cases left
  cases right
  simp_all

/-- Consecutive source-label ranges combine componentwise. -/
private theorem rhsSourceWeightLabelRangeLanes_add (laneWidth first second cursor : ℕ) :
    cert246Data.rhsSourceWeightLabelRangeLanes certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag (first + second) cursor =
      cert246Data.rhsWeightLanesMerge
        (cert246Data.rhsSourceWeightLabelRangeLanes certRhsDegreeBound certRhsSourceCs
          certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
          certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
          cert246Data.rhsSourceLocationT cert246Data.coeffMag first cursor)
        (cert246Data.rhsSourceWeightLabelRangeLanes certRhsDegreeBound certRhsSourceCs
          certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
          certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
          cert246Data.rhsSourceLocationT cert246Data.coeffMag second (cursor + first)) := by
  have hfull := rhsSourceWeightLabelRangeLanes_sound laneWidth (first + second) cursor
  have hfirst := rhsSourceWeightLabelRangeLanes_sound laneWidth first cursor
  have hsecond := rhsSourceWeightLabelRangeLanes_sound laneWidth second (cursor + first)
  rcases hfull with ⟨hfullBound, hfullPositive, hfullNegative⟩
  rcases hfirst with ⟨hfirstBound, hfirstPositive, hfirstNegative⟩
  rcases hsecond with ⟨hsecondBound, hsecondPositive, hsecondNegative⟩
  apply rhsWeightLanes_ext
  · simp only [cert246Data.rhsWeightLanesMerge, Nat.add_eq]
    rw [hfullBound, hfirstBound, hsecondBound, Finset.sum_range_add]
    simp only [Nat.add_assoc]
  · simp only [cert246Data.rhsWeightLanesMerge, Nat.add_eq]
    rw [hfullPositive, hfirstPositive, hsecondPositive, Finset.sum_range_add]
    simp only [Nat.add_assoc]
  · simp only [cert246Data.rhsWeightLanesMerge, Nat.add_eq]
    rw [hfullNegative, hfirstNegative, hsecondNegative, Finset.sum_range_add]
    simp only [Nat.add_assoc]

/-- The fixed-block source fold is extensionally the corresponding consecutive range scan. -/
private theorem rhsSourceWeightBlockRangeLanes_eq (laneWidth blockSize : ℕ) : ∀ count cursor,
    cert246Data.rhsSourceWeightBlockRangeLanes certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag blockSize count cursor =
      cert246Data.rhsSourceWeightLabelRangeLanes certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag (count * blockSize) cursor := by
  intro count
  induction count with
  | zero =>
      intro cursor
      simp [cert246Data.rhsSourceWeightBlockRangeLanes, cert246Data.rhsSourceWeightLabelRangeLanes]
  | succ count inductionHypothesis =>
      intro cursor
      simp only [cert246Data.rhsSourceWeightBlockRangeLanes]
      rw [inductionHypothesis]
      simpa only [Nat.add_eq, Nat.succ_mul, Nat.add_comm] using
        (rhsSourceWeightLabelRangeLanes_add laneWidth blockSize (count * blockSize) cursor).symm

/-- Chunking changes only the reduction tree, not the accumulated source lanes. -/
theorem rhsSourceWeightChunkedLanes_eq (laneWidth blockSize : ℕ) :
    cert246Data.rhsSourceWeightChunkedLanes certRhsLabelCount certRhsDegreeBound
        certRhsSourceCs certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask
        certRhsCoefficientWidth certRhsCoefficientMask laneWidth cert246Data.sigEnc
        cert246Data.labelEnc blockSize cert246Data.rhsSourceLocationT cert246Data.coeffMag =
      cert246Data.rhsSourceWeightLanes certRhsLabelCount certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag := by
  unfold cert246Data.rhsSourceWeightChunkedLanes cert246Data.rhsSourceWeightLanes
  by_cases hzero : blockSize = 0
  · subst blockSize
    rfl
  · have hpositive : Nat.blt 0 blockSize = true := Nat.blt_eq.mpr (Nat.pos_of_ne_zero hzero)
    rw [hpositive]
    change cert246Data.rhsWeightLanesMerge
      (cert246Data.rhsSourceWeightBlockRangeLanes certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag blockSize
        (certRhsLabelCount / blockSize) 0)
      (cert246Data.rhsSourceWeightLabelRangeLanes certRhsDegreeBound certRhsSourceCs
        certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
        certRhsCoefficientMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag (certRhsLabelCount % blockSize)
        (certRhsLabelCount / blockSize * blockSize)) = _
    rw [rhsSourceWeightBlockRangeLanes_eq]
    have hcombine := rhsSourceWeightLabelRangeLanes_add laneWidth
      ((certRhsLabelCount / blockSize) * blockSize) (certRhsLabelCount % blockSize) 0
    have hcount : certRhsLabelCount / blockSize * blockSize +
        certRhsLabelCount % blockSize = certRhsLabelCount := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod certRhsLabelCount blockSize
    rw [Nat.zero_add] at hcombine
    rw [hcount] at hcombine
    exact hcombine.symm

end PrimeGaps.Gap246
