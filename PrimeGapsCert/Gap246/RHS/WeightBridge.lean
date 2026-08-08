/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.ConcreteSound
public import PrimeGapsCert.Gap246.Sparse.WeightSound


/-! # Concrete bridge for the carry-free RHS feature-weight check -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

open Finset

/-- Successful first-order key checks for every source label. -/
def CertRhsFeatureKeyChecks : Prop :=
  ∀ label < 1295,
    cert246Data.rhsFeatureKeyLabelCheck 1504 25 10 1023 10 1023
      cert246Data.sigEnc cert246Data.labelEnc cert246Data.rhsFeatureEnc
      cert246Data.rhsSourceLocationT cert246Data.eraseTargetT label = true

private theorem certSignatureHasExponent_iff (row : Fin 272) (exponent : ℕ) :
    cert246Data.rhsSignatureHasExponent
        (cert246Data.sigField cert246Data.sigEnc row) exponent = true ↔
      exponent ∈ insert 0 (certSig row).toFinset := by
  rw [rhsSignatureHasExponent_sound, Finset.mem_insert]
  constructor
  · rintro (rfl | ⟨position, hposition, hvalue⟩)
    · exact Or.inl rfl
    · apply Or.inr
      apply List.mem_toFinset.mpr
      have hexponent : exponent ∈ PrimeGaps.Gap246.sigOf cert246Data.sigEnc row := by
        rw [PrimeGaps.Gap246.sigOf, PrimeGaps.Gap246.decodeSig_eq_map]
        simp only [Multiset.mem_coe, List.mem_map, List.mem_range]
        exact ⟨position, hposition, hvalue⟩
      rw [← certSig_coe row] at hexponent
      exact Multiset.mem_coe.mp hexponent
  · rintro (rfl | hexponent)
    · exact Or.inl rfl
    · apply Or.inr
      have hexponent' : exponent ∈ PrimeGaps.Gap246.sigOf cert246Data.sigEnc row := by
        rw [← certSig_coe row]
        exact Multiset.mem_coe.mpr (List.mem_toFinset.mp hexponent)
      rw [PrimeGaps.Gap246.sigOf, PrimeGaps.Gap246.decodeSig_eq_map] at hexponent'
      simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at hexponent'
      exact hexponent'

/-- The raw bounded-alphabet predicate recognizes exactly the mathematical transitions of one
source label. -/
theorem certRhsActive_iff (label : Fin 1295) (exponent : Fin 26) :
    certRhsActive label exponent = true ↔
      exponent.val ∈ insert 0 (certSig (certLabelSignature label)).toFinset := by
  unfold certRhsActive certRhsSignatureField certRhsLabelField
  change cert246Data.rhsSignatureHasExponent
      (cert246Data.sigField cert246Data.sigEnc (certLabelSignature label)) exponent = true ↔ _
  exact certSignatureHasExponent_iff (certLabelSignature label) exponent

private theorem certRhsSourceLocation_bound (hchecks : CertRhsFeatureKeyChecks) (label : ℕ)
    (hlabel : label < 1295) (exponent : ℕ) (hexponent : exponent < 26)
    (hactive : certRhsActive label exponent = true) :
    certRhsSourceLocation label exponent < 1504 := by
  let labelFin : Fin 1295 := ⟨label, hlabel⟩
  let exponentFin : Fin 26 := ⟨exponent, hexponent⟩
  have hexponentMem : exponent ∈ insert 0 (certSig (certLabelSignature labelFin)).toFinset :=
    (certRhsActive_iff labelFin exponentFin).mp hactive
  have hlabelCheck := rhsFeatureKeyLabelCheck_sound (hchecks label hlabel)
  have hentry : cert246Data.rhsFeatureKeyAt 1504 25 10 1023 10 1023
      cert246Data.labelEnc cert246Data.rhsFeatureEnc
      cert246Data.rhsSourceLocationT cert246Data.eraseTargetT label exponent = true := by
    rcases Finset.mem_insert.mp hexponentMem with hzero | hmember
    · simpa only [hzero] using hlabelCheck.1
    · have hmember' : exponent ∈ PrimeGaps.Gap246.sigOf cert246Data.sigEnc
          (certLabelSignature labelFin) := by
        rw [← certSig_coe (certLabelSignature labelFin)]
        exact Multiset.mem_coe.mpr (List.mem_toFinset.mp hmember)
      rw [PrimeGaps.Gap246.sigOf, PrimeGaps.Gap246.decodeSig_eq_map] at hmember'
      simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at hmember'
      obtain ⟨position, hposition, hvalue⟩ := hmember'
      have hposition' : position < cert246Data.sigCount
          (cert246Data.sigField cert246Data.sigEnc
            (cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label))) := by
        simpa only [certLabelSignature, certLabelField, labelFin] using hposition
      have hpositionCheck := hlabelCheck.2 position hposition'
      have hvalue' : 2 * cert246Data.sigNib
          (cert246Data.sigField cert246Data.sigEnc
            (cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label)))
            position = exponent := by
        simpa only [certLabelSignature, certLabelField, labelFin] using hvalue
      rwa [hvalue'] at hpositionCheck
  have hsound := rhsFeatureKeyAt_sound hentry
  dsimp only at hsound
  norm_num at hsound
  simpa only [certRhsSourceLocation, certRhsSourceCs, certRhsSourcePmask, certRhsDegreeBound]
    using hsound.1

/-- Every active concrete source transition addresses a valid packed feature lane. -/
theorem certRhsWeightLocations_bound (hchecks : CertRhsFeatureKeyChecks) :
    ∀ label < certRhsLabelCount, ∀ exponent < certRhsDegreeBound + 1,
      certRhsActive label exponent = true →
        certRhsSourceLocation label exponent < certRhsFeatureCount := by
  intro label hlabel exponent hexponent hactive
  apply certRhsSourceLocation_bound hchecks label
      (by simpa only [certRhsLabelCount] using hlabel) exponent
      (by simpa only [certRhsDegreeBound] using hexponent)
  simpa only using hactive

private theorem certRhsRawLocation (hchecks : CertRhsFeatureKeyChecks) (label : Fin 1295)
    (exponent : Fin 26)
    (hexponent : exponent.val ∈ insert 0 (certSig (certLabelSignature label)).toFinset) :
    certRhsSourceLocation label exponent =
      (preEpsWitnessInt.rhsLocateTransition certRhsLocations
        ⟨label, exponent.val, hexponent⟩).val := by
  have hactive := (certRhsActive_iff label exponent).mpr hexponent
  have hbound := certRhsSourceLocation_bound hchecks label label.isLt exponent
    exponent.isLt hactive
  unfold PreEpsCertificateExplicitDagInt.rhsLocateTransition certRhsLocations
  simp only [PreEpsCertificateExplicitDagInt.rhsTransitionExponent, Fin.val_mk]
  rw [Nat.mod_eq_of_lt]
  · rfl
  · simpa only [certRhsSourceLocation, certRhsSourceCs, certRhsSourcePmask, certRhsDegreeBound]
      using hbound

set_option exponentiation.threshold 1000 in
private theorem certRhsRawTransitionWeight (label : Fin 1295) (exponent : ℕ)
    (hexponent : exponent ∈ insert 0 (certSig (certLabelSignature label)).toFinset) :
    (if certRhsSign label = 0 then (certRhsMagnitude label exponent : ℤ)
      else - (certRhsMagnitude label exponent : ℤ)) =
      preEpsWitnessInt.rhsTransitionWeight certFactorTables ⟨label, exponent, hexponent⟩ := by
  simp only [certRhsSign, certRhsLabelField, certRhsMagnitude, certRhsCoefficientCs,
    certRhsCoefficientPmask, certRhsCoefficientWidth, certRhsCoefficientMask, certRhsDegreeBound]
  unfold PreEpsCertificateExplicitDagInt.rhsTransitionWeight
    certFactorTables directEpsPairFactorTables marginalFactorInt preEpsWitnessInt
    certLabelCoefficient certLabelA certLabelField
  dsimp only
  change (if cert246Data.labelSign (cert246Data.labelField cert246Data.labelEnc label) = 0 then
      ((cert246Data.treeAt 9 511 128 (2 ^ 128 - 1) cert246Data.coeffMag label *
        exponent ! *
        (cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label)) ! *
        Nat.descFactorial 26 (25 -
          (cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label) +
            exponent)) : ℕ) : ℤ)
    else - ((cert246Data.treeAt 9 511 128 (2 ^ 128 - 1) cert246Data.coeffMag label *
        exponent ! *
        (cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label)) ! *
        Nat.descFactorial 26 (25 -
          (cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label) +
            exponent)) : ℕ) : ℤ)) =
    (if cert246Data.labelSign (cert246Data.labelField cert246Data.labelEnc label) = 1 then
        -(cert246Data.treeAt 9 511 128 (2 ^ 128 - 1) cert246Data.coeffMag label : ℤ)
      else cert246Data.treeAt 9 511 128 (2 ^ 128 - 1) cert246Data.coeffMag label) *
      ((exponent ! *
        (cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label)) ! *
        Nat.descFactorial 26 (25 -
          (cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label) +
            exponent)) : ℕ) : ℤ)
  have hsign := labelSign_lt_two (cert246Data.labelField cert246Data.labelEnc label)
  by_cases hzero : cert246Data.labelSign (cert246Data.labelField cert246Data.labelEnc label) = 0
  · rw [if_pos hzero, if_neg (by omega)]
    push_cast
    ring
  · have hone : cert246Data.labelSign
        (cert246Data.labelField cert246Data.labelEnc label) = 1 := by omega
    rw [if_neg hzero, if_pos hone]
    push_cast
    ring

private theorem certRhsExponentSum (hchecks : CertRhsFeatureKeyChecks)
    (label : Fin 1295) (feature : Fin 1504) :
    (∑ exponent ∈ Finset.range 26,
      if certRhsActive label exponent = true ∧
          certRhsSourceLocation label exponent = feature.val then
        if certRhsSign label = 0 then (certRhsMagnitude label exponent : ℤ)
        else - (certRhsMagnitude label exponent : ℤ)
      else 0) =
      ∑ exponent ∈ (insert 0 (certSig (certLabelSignature label)).toFinset).attach,
        if preEpsWitnessInt.rhsLocateTransition certRhsLocations
            ⟨label, exponent.val, exponent.property⟩ = feature then
          preEpsWitnessInt.rhsTransitionWeight certFactorTables
            ⟨label, exponent.val, exponent.property⟩
        else 0 := by
  let exponents := insert 0 (certSig (certLabelSignature label)).toFinset
  let rawTerm : ℕ → ℤ := fun exponent ↦
    if certRhsSourceLocation label exponent = feature.val then
      if certRhsSign label = 0 then (certRhsMagnitude label exponent : ℤ)
      else - (certRhsMagnitude label exponent : ℤ)
    else 0
  calc
    (∑ exponent ∈ Finset.range 26,
        if certRhsActive label exponent = true ∧
            certRhsSourceLocation label exponent = feature.val then
          if certRhsSign label = 0 then (certRhsMagnitude label exponent : ℤ)
          else - (certRhsMagnitude label exponent : ℤ)
        else 0) =
        ∑ exponent ∈ Finset.range 26,
          if exponent ∈ exponents then rawTerm exponent else 0 := by
      apply Finset.sum_congr rfl
      intro exponent hexponent
      let exponentFin : Fin 26 := ⟨exponent, Finset.mem_range.mp hexponent⟩
      have hactive := certRhsActive_iff label exponentFin
      by_cases hmember : exponent ∈ exponents
      · have hactive' : certRhsActive label exponent = true := by
          apply hactive.mpr
          simpa only [exponents, exponentFin] using hmember
        simp [hactive', hmember, rawTerm]
      · have hactive' : certRhsActive label exponent ≠ true := by
          intro h
          apply hmember
          simpa only [exponents, exponentFin] using hactive.mp h
        simp [hactive', hmember]
    _ = ∑ exponent ∈ exponents, rawTerm exponent := by
      rw [← Finset.sum_filter]
      have hfilter : {exponent ∈ Finset.range 26 | exponent ∈ exponents} =
          exponents := by
        ext exponent
        simp only [Finset.mem_filter, Finset.mem_range]
        constructor
        · exact fun h ↦ h.2
        · intro hmember
          refine ⟨?_, hmember⟩
          rcases Finset.mem_insert.mp hmember with rfl | hsignature
          · norm_num
          · exact lt_trans
              (certSig_exponent_lt (certLabelSignature label) (certLabelSignature label).isLt
                exponent (List.mem_toFinset.mp hsignature)) (by norm_num)
      rw [hfilter]
    _ = ∑ exponent ∈ exponents.attach, rawTerm exponent.val :=
      (Finset.sum_attach exponents rawTerm).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro exponent hexponent
      have hexponentBound : exponent.val < 26 := by
        rcases Finset.mem_insert.mp exponent.property with hzero | hsignature
        · omega
        · exact lt_trans
            (certSig_exponent_lt (certLabelSignature label) (certLabelSignature label).isLt
              exponent.val (List.mem_toFinset.mp hsignature)) (by norm_num)
      let exponentFin : Fin 26 := ⟨exponent.val, hexponentBound⟩
      have hlocation := certRhsRawLocation hchecks label exponentFin exponent.property
      change certRhsSourceLocation label exponent.val =
        (preEpsWitnessInt.rhsLocateTransition certRhsLocations
          ⟨label, exponent.val, exponent.property⟩).val at hlocation
      have hweight := certRhsRawTransitionWeight label exponent.val exponent.property
      simp only [rawTerm]
      rw [hlocation, hweight]
      split_ifs <;> simp_all [Fin.ext_iff]

/-- The rectangular source scan is exactly the mathematical dependent-transition fiber. -/
theorem certRhsSourceDigit_correct (hchecks : CertRhsFeatureKeyChecks) (feature : Fin 1504) :
    (certRhsSourceDigit true feature : ℤ) - certRhsSourceDigit false feature =
      ∑ transition ∈ preEpsWitnessInt.rhsTransitions,
        if preEpsWitnessInt.rhsLocateTransition certRhsLocations transition = feature then
          preEpsWitnessInt.rhsTransitionWeight certFactorTables transition
        else 0 := by
  let rawFeature : Fin certRhsFeatureCount :=
    ⟨feature.val, by simpa only [certRhsFeatureCount] using feature.isLt⟩
  change (certRhsSourceDigit true rawFeature : ℤ) -
      certRhsSourceDigit false rawFeature = _
  rw [certRhsSourceDigit_sub]
  change (∑ label ∈ Finset.range 1295,
    ∑ exponent ∈ Finset.range 26,
      if certRhsActive label exponent = true ∧
          certRhsSourceLocation label exponent = feature.val then
        if certRhsSign label = 0 then (certRhsMagnitude label exponent : ℤ)
        else - (certRhsMagnitude label exponent : ℤ)
      else 0) = _
  rw [← Fin.sum_univ_eq_sum_range]
  rw [PreEpsCertificateExplicitDagInt.rhsTransitions, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro label hlabel
  exact certRhsExponentSum hchecks label feature

/-- Pointwise correctness of the raw carry-free lanes supplies the mathematical feature-weight
specification. -/
theorem certRhsFeatureWeights_of_raw (hchecks : CertRhsFeatureKeyChecks)
    (hraw : ∀ feature : Fin 1504,
      signedValue (certRhsExpectedWeight feature) =
        (certRhsSourceDigit true feature : ℤ) - certRhsSourceDigit false feature) :
    ∀ feature,
      RhsMarginalFeature.WeightCorrectAt preEpsWitnessInt certFactorTables certRhsFeature
        certRhsLocations feature := by
  intro feature
  unfold RhsMarginalFeature.WeightCorrectAt
  rw [← certRhsSourceDigit_correct hchecks feature]
  simpa only [certRhsFeature, certRhsExpectedWeight, certRhsWeightCs, certRhsWeightPmask,
    certRhsWeightWidth, certRhsWeightMask] using hraw feature

end PrimeGaps.Gap246
