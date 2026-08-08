/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.WeightExpected


/-! # Checkpoint soundness for packed RHS weights -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- A successful componentwise lane comparison is equality of the records. -/
theorem rhsWeightLanesEqCheck_sound {actual expected : cert246Data.RhsWeightLanes}
    (hcheck : cert246Data.rhsWeightLanesEqCheck actual expected = true) :
    actual = expected := by
  unfold cert246Data.rhsWeightLanesEqCheck at hcheck
  simp only [Bool.and'_eq_and, Bool.and_eq_true, Nat.beq_eq] at hcheck
  exact rhsWeightLanes_ext hcheck.1 hcheck.2.1 hcheck.2.2

/-- Verified source checkpoints replace every full block in the bounded block fold. -/
private theorem rhsSourceWeightBlockRangeLanes_eq_checkpoints (laneWidth blockSize : ℕ)
    (bound positive negative : Lean.RArray ℕ)
    (hchecks : ∀ block < certRhsLabelCount / blockSize,
      certRhsSourceCheckpointBlockCheck laneWidth blockSize block bound positive negative =
        true) :
    ∀ count block, block + count ≤ certRhsLabelCount / blockSize →
      cert246Data.rhsSourceWeightBlockRangeLanes certRhsDegreeBound certRhsSourceCs
          certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask
          certRhsCoefficientWidth certRhsCoefficientMask laneWidth cert246Data.sigEnc
          cert246Data.labelEnc cert246Data.rhsSourceLocationT cert246Data.coeffMag blockSize
          count (block * blockSize) =
        cert246Data.rhsSourceWeightCheckpointFold bound positive negative count block := by
  intro count
  induction count with
  | zero =>
      intro block _
      simp [cert246Data.rhsSourceWeightBlockRangeLanes,
        cert246Data.rhsSourceWeightCheckpointFold]
  | succ count inductionHypothesis =>
      intro block hbound
      have hblock : block < certRhsLabelCount / blockSize := by omega
      have hcheck := hchecks block hblock
      unfold certRhsSourceCheckpointBlockCheck
        cert246Data.rhsSourceWeightCheckpointBlockCheck at hcheck
      have hfull : Nat.blt block (certRhsLabelCount / blockSize) = true :=
        Nat.blt_eq.mpr hblock
      simp only [hfull, Nat.mul_eq] at hcheck
      have hhead := rhsWeightLanesEqCheck_sound hcheck
      simp only [cert246Data.rhsSourceWeightBlockRangeLanes,
        cert246Data.rhsSourceWeightCheckpointFold, Nat.add_eq]
      rw [show block * blockSize + blockSize = (block + 1) * blockSize by
        simp only [Nat.add_mul, one_mul]]
      rw [inductionHypothesis (block + 1) (by omega), hhead]

/-- Verified expected checkpoints replace every full block in the bounded block fold. -/
private theorem rhsExpectedWeightBlockRangeLanes_eq_checkpoints (laneWidth blockSize : ℕ)
    (bound positive negative : Lean.RArray ℕ)
    (hchecks : ∀ block < certRhsFeatureCount / blockSize,
      certRhsExpectedCheckpointBlockCheck laneWidth blockSize block bound positive negative =
        true) :
    ∀ count block, block + count ≤ certRhsFeatureCount / blockSize →
      cert246Data.rhsExpectedWeightBlockRangeLanes certRhsWeightCs certRhsWeightPmask
          certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT blockSize count
          (block * blockSize) =
        cert246Data.rhsExpectedWeightCheckpointFold bound positive negative count block := by
  intro count
  induction count with
  | zero =>
      intro block _
      simp [cert246Data.rhsExpectedWeightBlockRangeLanes,
        cert246Data.rhsExpectedWeightCheckpointFold]
  | succ count inductionHypothesis =>
      intro block hbound
      have hblock : block < certRhsFeatureCount / blockSize := by omega
      have hcheck := hchecks block hblock
      unfold certRhsExpectedCheckpointBlockCheck
        cert246Data.rhsExpectedWeightCheckpointBlockCheck at hcheck
      have hfull : Nat.blt block (certRhsFeatureCount / blockSize) = true :=
        Nat.blt_eq.mpr hblock
      simp only [hfull, Nat.mul_eq] at hcheck
      have hhead := rhsWeightLanesEqCheck_sound hcheck
      simp only [cert246Data.rhsExpectedWeightBlockRangeLanes,
        cert246Data.rhsExpectedWeightCheckpointFold, Nat.add_eq]
      rw [show block * blockSize + blockSize = (block + 1) * blockSize by
        simp only [Nat.add_mul, one_mul]]
      rw [inductionHypothesis (block + 1) (by omega), hhead]

/-- All verified source blocks identify the chunked source fold with its proposed checkpoints. -/
theorem rhsSourceWeightChunkedLanes_eq_checkpoints (laneWidth blockSize : ℕ)
    (bound positive negative : Lean.RArray ℕ)
    (hpositive : 0 < blockSize)
    (hchecks : ∀ block < certRhsLabelCount / blockSize + 1,
      certRhsSourceCheckpointBlockCheck laneWidth blockSize block bound positive negative =
        true) :
    cert246Data.rhsSourceWeightChunkedLanes certRhsLabelCount certRhsDegreeBound
        certRhsSourceCs certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask
        certRhsCoefficientWidth certRhsCoefficientMask laneWidth cert246Data.sigEnc
        cert246Data.labelEnc blockSize cert246Data.rhsSourceLocationT cert246Data.coeffMag =
      cert246Data.rhsWeightLanesMerge
        (cert246Data.rhsSourceWeightCheckpointFold bound positive negative
          (certRhsLabelCount / blockSize) 0)
        (cert246Data.rhsWeightCheckpointAt bound positive negative
          (certRhsLabelCount / blockSize)) := by
  unfold cert246Data.rhsSourceWeightChunkedLanes
  have hrawPositive : Nat.blt 0 blockSize = true := Nat.blt_eq.mpr hpositive
  rw [hrawPositive]
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
  have hfold := rhsSourceWeightBlockRangeLanes_eq_checkpoints laneWidth blockSize bound
    positive negative (fun block hblock ↦ hchecks block (by omega))
    (certRhsLabelCount / blockSize) 0 (by omega)
  simp only [Nat.zero_mul] at hfold
  rw [hfold]
  have hremainder := hchecks (certRhsLabelCount / blockSize) (by omega)
  unfold certRhsSourceCheckpointBlockCheck
    cert246Data.rhsSourceWeightCheckpointBlockCheck at hremainder
  have hself : Nat.blt (certRhsLabelCount / blockSize)
      (certRhsLabelCount / blockSize) = false :=
    Bool.eq_false_of_not_eq_true fun h ↦ (Nat.blt_eq.mp h).false
  simp only [hself, Nat.mul_eq] at hremainder
  rw [rhsWeightLanesEqCheck_sound hremainder]

/-- All verified expected blocks identify the chunked feature fold with its checkpoints. -/
theorem rhsExpectedWeightChunkedLanes_eq_checkpoints (laneWidth blockSize : ℕ)
    (bound positive negative : Lean.RArray ℕ)
    (hpositive : 0 < blockSize)
    (hchecks : ∀ block < certRhsFeatureCount / blockSize + 1,
      certRhsExpectedCheckpointBlockCheck laneWidth blockSize block bound positive negative =
        true) :
    cert246Data.rhsExpectedWeightChunkedLanes certRhsFeatureCount certRhsWeightCs
        certRhsWeightPmask certRhsWeightWidth certRhsWeightMask laneWidth blockSize
        cert246Data.rhsWeightT =
      cert246Data.rhsExpectedWeightLanesMerge
        (cert246Data.rhsExpectedWeightCheckpointFold bound positive negative
          (certRhsFeatureCount / blockSize) 0)
        (cert246Data.rhsWeightCheckpointAt bound positive negative
          (certRhsFeatureCount / blockSize)) := by
  unfold cert246Data.rhsExpectedWeightChunkedLanes
  have hrawPositive : Nat.blt 0 blockSize = true := Nat.blt_eq.mpr hpositive
  rw [hrawPositive]
  change cert246Data.rhsExpectedWeightLanesMerge
    (cert246Data.rhsExpectedWeightBlockRangeLanes certRhsWeightCs certRhsWeightPmask
      certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT blockSize
      (certRhsFeatureCount / blockSize) 0)
    (cert246Data.rhsExpectedWeightRangeLanes certRhsWeightCs certRhsWeightPmask
      certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT
      (certRhsFeatureCount % blockSize) (certRhsFeatureCount / blockSize * blockSize)) = _
  have hfold := rhsExpectedWeightBlockRangeLanes_eq_checkpoints laneWidth blockSize bound
    positive negative (fun block hblock ↦ hchecks block (by omega))
    (certRhsFeatureCount / blockSize) 0 (by omega)
  simp only [Nat.zero_mul] at hfold
  rw [hfold]
  have hremainder := hchecks (certRhsFeatureCount / blockSize) (by omega)
  unfold certRhsExpectedCheckpointBlockCheck
    cert246Data.rhsExpectedWeightCheckpointBlockCheck at hremainder
  have hself : Nat.blt (certRhsFeatureCount / blockSize)
      (certRhsFeatureCount / blockSize) = false :=
    Bool.eq_false_of_not_eq_true fun h ↦ (Nat.blt_eq.mp h).false
  simp only [hself, Nat.mul_eq] at hremainder
  rw [rhsWeightLanesEqCheck_sound hremainder]

/-- Independently verified partial lanes imply the original global RHS weight check. -/
theorem rhsWeightEncodingCheck_of_checkpoints (laneWidth sourceBlockSize expectedBlockSize : ℕ)
    (sourceBound sourcePositive sourceNegative expectedBound expectedPositive expectedNegative :
      Lean.RArray ℕ)
    (hsourcePositive : 0 < sourceBlockSize) (hexpectedPositive : 0 < expectedBlockSize)
    (hsource : ∀ block < certRhsLabelCount / sourceBlockSize + 1,
      certRhsSourceCheckpointBlockCheck laneWidth sourceBlockSize block sourceBound
        sourcePositive sourceNegative = true)
    (hexpected : ∀ block < certRhsFeatureCount / expectedBlockSize + 1,
      certRhsExpectedCheckpointBlockCheck laneWidth expectedBlockSize block expectedBound
        expectedPositive expectedNegative = true)
    (hbalance : cert246Data.rhsWeightCheckpointBalanceCheck laneWidth
      (certRhsLabelCount / sourceBlockSize) (certRhsFeatureCount / expectedBlockSize)
      sourceBound sourcePositive sourceNegative expectedBound expectedPositive expectedNegative =
        true) :
    cert246Data.rhsWeightEncodingCheck certRhsLabelCount certRhsFeatureCount certRhsDegreeBound
        certRhsSourceCs certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask
        certRhsCoefficientWidth certRhsCoefficientMask certRhsWeightCs certRhsWeightPmask
        certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.sigEnc cert246Data.labelEnc
        cert246Data.rhsSourceLocationT cert246Data.coeffMag cert246Data.rhsWeightT = true := by
  unfold cert246Data.rhsWeightEncodingCheck
  rw [← rhsSourceWeightChunkedLanes_eq laneWidth sourceBlockSize,
    ← rhsExpectedWeightChunkedLanes_eq laneWidth expectedBlockSize]
  rw [rhsSourceWeightChunkedLanes_eq_checkpoints laneWidth sourceBlockSize sourceBound
      sourcePositive sourceNegative hsourcePositive hsource,
    rhsExpectedWeightChunkedLanes_eq_checkpoints laneWidth expectedBlockSize expectedBound
      expectedPositive expectedNegative hexpectedPositive hexpected]
  simpa only [cert246Data.rhsWeightCheckpointBalanceCheck] using hbalance

end PrimeGaps.Gap246
