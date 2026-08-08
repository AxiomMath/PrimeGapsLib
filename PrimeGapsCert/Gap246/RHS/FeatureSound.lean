/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Checks.Weight
public import PrimeGapsCert.Gap246.RHS.WeightBridge


/-! # Soundness of the packed RHS marginal-feature aggregation -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Location of one dependent marginal transition in the packed feature table. -/
noncomputable def certRhsLocate (transition : preEpsWitnessInt.RhsTransition) : Fin 1504 :=
  preEpsWitnessInt.rhsLocateTransition certRhsLocations transition

/-- Every stored marginal-feature weight equals its complete mathematical transition fiber. -/
def CertRhsWeightEncoding : Prop :=
  ∀ feature,
    RhsMarginalFeature.WeightCorrectAt preEpsWitnessInt certFactorTables certRhsFeature
      certRhsLocations feature

set_option maxRecDepth 100000 in
set_option exponentiation.threshold 1000 in
/-- The carry-free packed identity certifies every marginal-feature weight. -/
theorem certRhsWeightEncoding_complete
    (hchecks : CertRhsFeatureKeyChecks) : CertRhsWeightEncoding := by
  have hcheck : cert246Data.rhsWeightEncodingCheck certRhsLabelCount certRhsFeatureCount
      certRhsDegreeBound certRhsSourceCs certRhsSourcePmask certRhsCoefficientCs
      certRhsCoefficientPmask certRhsCoefficientWidth certRhsCoefficientMask certRhsWeightCs
      certRhsWeightPmask certRhsWeightWidth certRhsWeightMask cert246Data.rhsWeightLaneWidth
      cert246Data.sigEnc cert246Data.labelEnc cert246Data.rhsSourceLocationT
      cert246Data.coeffMag cert246Data.rhsWeightT = true := by
    have hsource :
        ∀ block < certRhsLabelCount / cert246Data.rhsSourceWeightBlockSize + 1,
          certRhsSourceCheckpointBlockCheck cert246Data.rhsWeightLaneWidth
            cert246Data.rhsSourceWeightBlockSize block
            cert246Data.rhsSourceWeightBoundCheckpoint
            cert246Data.rhsSourceWeightPositiveCheckpoint
            cert246Data.rhsSourceWeightNegativeCheckpoint = true := by
      intro block hblock
      have hfin : block < 41 := by
        simpa only [certRhsLabelCount, cert246Data.rhsSourceWeightBlockSize] using hblock
      simpa only [CertRhsSourceWeightBlockCorrect, certRhsSourceCheckpointBlockCheck,
        certRhsLabelCount, certRhsDegreeBound, certRhsSourceCs, certRhsSourcePmask,
        certRhsCoefficientCs, certRhsCoefficientPmask, certRhsCoefficientWidth,
        certRhsCoefficientMask] using certRhsSourceWeightBlockChecks ⟨block, hfin⟩
    have hexpected :
        ∀ block < certRhsFeatureCount / cert246Data.rhsExpectedWeightBlockSize + 1,
          certRhsExpectedCheckpointBlockCheck cert246Data.rhsWeightLaneWidth
            cert246Data.rhsExpectedWeightBlockSize block
            cert246Data.rhsExpectedWeightBoundCheckpoint
            cert246Data.rhsExpectedWeightPositiveCheckpoint
            cert246Data.rhsExpectedWeightNegativeCheckpoint = true := by
      intro block hblock
      have hfin : block < 24 := by
        simpa only [certRhsFeatureCount, cert246Data.rhsExpectedWeightBlockSize] using hblock
      simpa only [CertRhsExpectedWeightBlockCorrect, certRhsExpectedCheckpointBlockCheck,
        certRhsFeatureCount, certRhsWeightCs, certRhsWeightPmask, certRhsWeightWidth,
        certRhsWeightMask] using certRhsExpectedWeightBlockChecks ⟨block, hfin⟩
    apply rhsWeightEncodingCheck_of_checkpoints cert246Data.rhsWeightLaneWidth
      cert246Data.rhsSourceWeightBlockSize cert246Data.rhsExpectedWeightBlockSize
      cert246Data.rhsSourceWeightBoundCheckpoint
      cert246Data.rhsSourceWeightPositiveCheckpoint
      cert246Data.rhsSourceWeightNegativeCheckpoint
      cert246Data.rhsExpectedWeightBoundCheckpoint
      cert246Data.rhsExpectedWeightPositiveCheckpoint
      cert246Data.rhsExpectedWeightNegativeCheckpoint
    · decide +kernel
    · decide +kernel
    · exact hsource
    · exact hexpected
    · simpa only [CertRhsWeightCheckpointBalanceCorrect, certRhsLabelCount,
        certRhsFeatureCount] using certRhsWeightCheckpointBalance
  have hraw := rhsWeightEncodingCheck_sound cert246Data.rhsWeightLaneWidth
    (by decide +kernel)
    (certRhsWeightLocations_bound hchecks)
    hcheck
  exact certRhsFeatureWeights_of_raw hchecks hraw

private theorem certSig_mem_position {row : Fin 272} {exponent : ℕ}
    (hexponent : exponent ∈ certSig row) :
    ∃ position < cert246Data.sigCount
        (cert246Data.sigField cert246Data.sigEnc row),
      2 * cert246Data.sigNib
        (cert246Data.sigField cert246Data.sigEnc row) position = exponent := by
  have hexponent' : exponent ∈ PrimeGaps.Gap246.sigOf cert246Data.sigEnc row := by
    rw [← certSig_coe row]
    exact Multiset.mem_coe.mpr hexponent
  rw [PrimeGaps.Gap246.sigOf, PrimeGaps.Gap246.decodeSig_eq_map] at hexponent'
  simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at hexponent'
  obtain ⟨position, hposition, hvalue⟩ := hexponent'
  exact ⟨position, hposition, hvalue⟩

/-- The checked packed location of one valid transition has the complete mathematical key. -/
theorem certRhsFeatureKey (hchecks : CertRhsFeatureKeyChecks) (label : Fin 1295)
    (exponent : Fin 26)
    (hexponent : exponent.val ∈ insert 0 (certSig (certLabelSignature label)).toFinset) :
    (certRhsFeature (certRhsLocations label exponent)).signature =
        certErase (certLabelSignature label) exponent.val ∧
      (certRhsFeature (certRhsLocations label exponent)).residualDegree =
        (certSig (certLabelSignature label)).sum - exponent.val ∧
      (certRhsFeature (certRhsLocations label exponent)).radialDegree =
        certLabelA label + exponent.val + 1 := by
  let labelField := cert246Data.labelField cert246Data.labelEnc label
  let sourceSignature := cert246Data.labelSignature labelField
  let rawLocation := cert246Data.treeAt 10 1023 16 65535
    cert246Data.rhsSourceLocationT (label * 26 + exponent)
  let rawErase := cert246Data.treeAt 10 1023 16 65535 cert246Data.eraseTargetT
    (sourceSignature * 26 + exponent)
  have hlabel := rhsFeatureKeyLabelCheck_sound (hchecks label label.isLt)
  have hsource : sourceSignature < 272 :=
    (certLabels label label.isLt).1
  have hentry : cert246Data.rhsFeatureKeyAt 1504 25 10 1023 10 1023
      cert246Data.labelEnc cert246Data.rhsFeatureEnc
      cert246Data.rhsSourceLocationT cert246Data.eraseTargetT label exponent = true := by
    rcases Finset.mem_insert.mp hexponent with hzero | hmember
    · have hzero' : exponent.val = 0 := hzero
      simpa only [hzero'] using hlabel.1
    · obtain ⟨position, hposition, hvalue⟩ :=
        certSig_mem_position (List.mem_toFinset.mp hmember)
      have hposition' : position < cert246Data.sigCount
          (cert246Data.sigField cert246Data.sigEnc sourceSignature) := by
        simpa only [certLabelSignature, certLabelField, labelField, sourceSignature]
          using hposition
      have hvalue' : 2 * cert246Data.sigNib
          (cert246Data.sigField cert246Data.sigEnc sourceSignature) position =
          exponent.val := by
        simpa only [certLabelSignature, certLabelField, labelField, sourceSignature]
          using hvalue
      have hpositionCheck := hlabel.2 position hposition'
      rw [hvalue'] at hpositionCheck
      exact hpositionCheck
  have hraw := rhsFeatureKeyAt_sound hentry
  dsimp only at hraw
  norm_num at hraw
  have hlocation : rawLocation < 1504 :=
    hraw.1
  have heraseBound : rawErase < 272 := by
    rcases Finset.mem_insert.mp hexponent with hzero | hmember
    · have hid := (eraseTargetCheck_sound cert246Data.erase_target_ok
        sourceSignature hsource).1
      have hzero' : exponent.val = 0 := hzero
      dsimp only [rawErase]
      rw [hzero']
      norm_num at hid ⊢
      rw [hid]
      exact hsource
    · obtain ⟨position, hposition, hvalue⟩ :=
        certSig_mem_position (List.mem_toFinset.mp hmember)
      have htarget := (eraseTargetCheck_sound cert246Data.erase_target_ok
        sourceSignature hsource).2 position (by
          simpa only [certLabelSignature, certLabelField, labelField,
            sourceSignature] using hposition)
      have hvalue' : 2 * cert246Data.sigNib
          (cert246Data.sigField cert246Data.sigEnc sourceSignature) position =
          exponent.val := by
        simpa only [certLabelSignature, certLabelField, labelField, sourceSignature]
          using hvalue
      dsimp only at htarget
      norm_num at htarget
      rw [hvalue'] at htarget
      exact htarget.1
  have hlocationEq : certRhsLocations label exponent = ⟨rawLocation, hlocation⟩ := by
    unfold certRhsLocations
    exact Fin.ext (Nat.mod_eq_of_lt hlocation)
  have heraseEq : certErase (certLabelSignature label) exponent.val =
      ⟨rawErase, heraseBound⟩ := by
    unfold certErase
    by_cases hzero : exponent.val = 0
    · rw [if_pos hzero]
      apply Fin.ext
      have hid := (eraseTargetCheck_sound cert246Data.erase_target_ok
        sourceSignature hsource).1
      dsimp only [rawErase, certLabelSignature, sourceSignature, labelField]
      rw [hzero]
      exact hid.symm
    · rw [if_neg hzero]
      exact Fin.ext (Nat.mod_eq_of_lt heraseBound)
  rw [hlocationEq, heraseEq]
  constructor
  · apply Fin.ext
    unfold certRhsFeature
    dsimp only
    rw [hraw.2.1, Nat.mod_eq_of_lt heraseBound]
  · constructor
    · change cert246Data.rhsFeatureResidual
          (cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc rawLocation) = _
      rw [hraw.2.2.1]
      congr 1
      rw [certSig_sum]
      simpa only [certLabelSignature, certLabelField, labelField] using
        (certLabels label label.isLt).2.1
    · change cert246Data.rhsFeatureRadial
          (cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc rawLocation) = _
      simpa only [certLabelA, certLabelField, labelField] using hraw.2.2.2

/-- All checked label-and-erasure locations have the required marginal-feature keys. -/
theorem certRhsFeatureKeys_correct (hchecks : CertRhsFeatureKeyChecks) : ∀ label,
    RhsMarginalFeature.KeyCorrectAt preEpsWitnessInt certRhsFeature certRhsLocations label := by
  intro label exponent
  split_ifs with hexponent
  · exact certRhsFeatureKey hchecks label exponent hexponent

/-- The global signed encoding recovers every pointwise marginal-feature weight fiber. -/
theorem certRhsFeatureWeights_correct (hencoding : CertRhsWeightEncoding) : ∀ feature,
    RhsMarginalFeature.WeightCorrectAt preEpsWitnessInt certFactorTables certRhsFeature
      certRhsLocations feature :=
  hencoding

/-- Checked keys and weights make the packed features reproduce every marginal transition. -/
theorem certRhsFeatures_correct (hkeys : CertRhsFeatureKeyChecks)
    (hweights : CertRhsWeightEncoding) :
    RhsMarginalFeature.Correct preEpsWitnessInt certFactorTables certRhsFeature := by
  apply RhsMarginalFeature.correct_of_locationCorrect preEpsWitnessInt certFactorTables
    certRhsFeature certRhsLocate
  change RhsMarginalFeature.LocationCorrect preEpsWitnessInt certFactorTables certRhsFeature
    (preEpsWitnessInt.rhsLocateTransition certRhsLocations)
  exact RhsMarginalFeature.locationCorrect_of_checks preEpsWitnessInt certFactorTables
    certRhsFeature certRhsLocations (certRhsFeatureKeys_correct hkeys)
    (certRhsFeatureWeights_correct hweights)

/-- Complete checked feature keys also certify the packed feature weights and aggregation. -/
theorem certRhsFeatures_of_keyChecks (hkeys : CertRhsFeatureKeyChecks) :
    RhsMarginalFeature.Correct preEpsWitnessInt certFactorTables certRhsFeature := by
  apply certRhsFeatures_correct hkeys
  exact certRhsWeightEncoding_complete hkeys

end PrimeGaps.Gap246
