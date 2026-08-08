/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.WeightSource


/-! # Expected-fold soundness for packed RHS weights -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- The expected-feature range fold equals its direct bounded finite sums. -/
theorem rhsExpectedWeightRangeLanes_sound (laneWidth : ℕ) :
    ∀ count cursor,
      let result := cert246Data.rhsExpectedWeightRangeLanes certRhsWeightCs certRhsWeightPmask
        certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT count cursor
      result.positive = (
          ∑ offset ∈ Finset.range count,
            let feature := cursor + offset
            let value := certRhsExpectedWeight feature
            if cert246Data.signedSign value = 0 then
              Nat.shiftLeft (cert246Data.signedMagnitude value)
                (laneWidth * feature)
            else 0) ∧
        result.negative = (
          ∑ offset ∈ Finset.range count,
            let feature := cursor + offset
            let value := certRhsExpectedWeight feature
            if cert246Data.signedSign value = 0 then 0
            else Nat.shiftLeft (cert246Data.signedMagnitude value)
              (laneWidth * feature)) ∧
        ∀ feature, cursor ≤ feature → feature < cursor + count →
          cert246Data.signedMagnitude (certRhsExpectedWeight feature) ≤ result.bound := by
  intro count
  induction count with
  | zero =>
      intro cursor
      simp [cert246Data.rhsExpectedWeightRangeLanes]
      omega
  | succ count inductionHypothesis =>
      intro cursor
      dsimp only
      rw [sum_range_head (fun feature ↦
        let value := certRhsExpectedWeight feature
        if cert246Data.signedSign value = 0 then
          Nat.shiftLeft (cert246Data.signedMagnitude value) (laneWidth * feature)
        else 0) cursor count]
      rw [sum_range_head (fun feature ↦
        let value := certRhsExpectedWeight feature
        if cert246Data.signedSign value = 0 then 0
        else Nat.shiftLeft (cert246Data.signedMagnitude value) (laneWidth * feature))
        cursor count]
      simp only [cert246Data.rhsExpectedWeightRangeLanes]
      rcases inductionHypothesis cursor.succ with ⟨hpositive, hnegative, hbound⟩
      let value := certRhsExpectedWeight cursor
      have hexpected : cert246Data.treeAt certRhsWeightCs certRhsWeightPmask certRhsWeightWidth
          certRhsWeightMask cert246Data.rhsWeightT cursor =
          certRhsExpectedWeight cursor := rfl
      rw [hexpected]
      by_cases hsign : cert246Data.signedSign value = 0
      · have hsignExpected : cert246Data.signedSign (certRhsExpectedWeight cursor) = 0 := by
          simpa only [value] using hsign
        simp only [hsignExpected, if_pos]
        constructor
        · rw [hpositive]
          simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
        · constructor
          · rw [hnegative]
            simp only [zero_add, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
          · intro feature hlower hupper
            rcases Nat.eq_or_lt_of_le hlower with rfl | hlower
            · exact Nat.le_max_right _ _
            · exact (hbound feature (by omega) (by omega)).trans (Nat.le_max_left _ _)
      · have hsignExpected : cert246Data.signedSign (certRhsExpectedWeight cursor) ≠ 0 := by
          simpa only [value] using hsign
        simp only [hsignExpected, if_false]
        constructor
        · rw [hpositive]
          simp only [zero_add, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
        · constructor
          · rw [hnegative]
            simp only [Nat.add_eq, Nat.mul_eq, Nat.succ_eq_add_one, Nat.add_comm, Nat.add_left_comm]
          · intro feature hlower hupper
            rcases Nat.eq_or_lt_of_le hlower with rfl | hlower
            · exact Nat.le_max_right _ _
            · exact (hbound feature (by omega) (by omega)).trans (Nat.le_max_left _ _)

/-- Consecutive expected-feature ranges combine with maximum digit bound. -/
private theorem rhsExpectedWeightRangeLanes_add (laneWidth : ℕ) :
    ∀ first second cursor,
    cert246Data.rhsExpectedWeightRangeLanes certRhsWeightCs certRhsWeightPmask
        certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT
        (first + second) cursor =
      cert246Data.rhsExpectedWeightLanesMerge
        (cert246Data.rhsExpectedWeightRangeLanes certRhsWeightCs certRhsWeightPmask
          certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT first cursor)
        (cert246Data.rhsExpectedWeightRangeLanes certRhsWeightCs certRhsWeightPmask
          certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT second
          (cursor + first)) := by
  intro first
  induction first with
  | zero =>
      intro second cursor
      simp [cert246Data.rhsExpectedWeightRangeLanes,
        cert246Data.rhsExpectedWeightLanesMerge]
  | succ first inductionHypothesis =>
      intro second cursor
      rw [Nat.succ_add]
      simp only [cert246Data.rhsExpectedWeightRangeLanes]
      rw [inductionHypothesis second (cursor + 1)]
      rw [show cursor + 1 + first = cursor + (first + 1) by omega]
      by_cases hsign : cert246Data.signedSign
          (cert246Data.treeAt certRhsWeightCs certRhsWeightPmask certRhsWeightWidth
            certRhsWeightMask cert246Data.rhsWeightT cursor) = 0
      · simp only [if_pos hsign, Nat.succ_eq_add_one]
        apply rhsWeightLanes_ext <;>
          simp only [cert246Data.rhsExpectedWeightLanesMerge, Nat.add_eq] <;> omega
      · simp only [if_neg hsign, Nat.succ_eq_add_one]
        apply rhsWeightLanes_ext <;>
          simp only [cert246Data.rhsExpectedWeightLanesMerge, Nat.add_eq] <;> omega

/-- The fixed-block expected fold is extensionally the corresponding consecutive range scan. -/
private theorem rhsExpectedWeightBlockRangeLanes_eq (laneWidth blockSize : ℕ) : ∀ count cursor,
    cert246Data.rhsExpectedWeightBlockRangeLanes certRhsWeightCs certRhsWeightPmask
        certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT blockSize count
        cursor =
      cert246Data.rhsExpectedWeightRangeLanes certRhsWeightCs certRhsWeightPmask
        certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT
        (count * blockSize) cursor := by
  intro count
  induction count with
  | zero =>
      intro cursor
      simp [cert246Data.rhsExpectedWeightBlockRangeLanes,
        cert246Data.rhsExpectedWeightRangeLanes]
  | succ count inductionHypothesis =>
      intro cursor
      simp only [cert246Data.rhsExpectedWeightBlockRangeLanes]
      rw [inductionHypothesis]
      simpa only [Nat.add_eq, Nat.succ_mul, Nat.add_comm] using
        (rhsExpectedWeightRangeLanes_add laneWidth blockSize (count * blockSize) cursor).symm

/-- Chunking changes only the reduction tree of the expected-weight lanes. -/
theorem rhsExpectedWeightChunkedLanes_eq (laneWidth blockSize : ℕ) :
    cert246Data.rhsExpectedWeightChunkedLanes certRhsFeatureCount certRhsWeightCs
        certRhsWeightPmask certRhsWeightWidth certRhsWeightMask laneWidth blockSize
        cert246Data.rhsWeightT =
      cert246Data.rhsExpectedWeightLanes certRhsFeatureCount certRhsWeightCs
        certRhsWeightPmask certRhsWeightWidth certRhsWeightMask laneWidth
        cert246Data.rhsWeightT := by
  unfold cert246Data.rhsExpectedWeightChunkedLanes cert246Data.rhsExpectedWeightLanes
  by_cases hzero : blockSize = 0
  · subst blockSize
    rfl
  · have hpositive : Nat.blt 0 blockSize = true :=
      Nat.blt_eq.mpr (Nat.pos_of_ne_zero hzero)
    rw [hpositive]
    change cert246Data.rhsExpectedWeightLanesMerge
      (cert246Data.rhsExpectedWeightBlockRangeLanes certRhsWeightCs certRhsWeightPmask
        certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT blockSize
        (certRhsFeatureCount / blockSize) 0)
      (cert246Data.rhsExpectedWeightRangeLanes certRhsWeightCs certRhsWeightPmask
        certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT
        (certRhsFeatureCount % blockSize) (certRhsFeatureCount / blockSize * blockSize)) = _
    rw [rhsExpectedWeightBlockRangeLanes_eq]
    have hcombine := rhsExpectedWeightRangeLanes_add laneWidth
      ((certRhsFeatureCount / blockSize) * blockSize) (certRhsFeatureCount % blockSize) 0
    have hcount : certRhsFeatureCount / blockSize * blockSize +
        certRhsFeatureCount % blockSize = certRhsFeatureCount := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod certRhsFeatureCount blockSize
    rw [Nat.zero_add] at hcombine
    rw [hcount] at hcombine
    exact hcombine.symm

end PrimeGaps.Gap246
