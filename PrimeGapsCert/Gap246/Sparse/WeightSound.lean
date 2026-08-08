/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.WeightDigits


/-! # Final soundness of carry-free packed RHS weight lanes -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- A successful carry-free raw check recovers every proposed signed feature weight as the
difference of its positive and negative source-transition fibers. -/
theorem rhsWeightEncodingCheck_sound (laneWidth : ℕ) (hlaneWidth : 0 < laneWidth)
    (hlocation : ∀ label < certRhsLabelCount, ∀ exponent < certRhsDegreeBound + 1,
      certRhsActive label exponent = true →
        certRhsSourceLocation label exponent < certRhsFeatureCount)
    (hcheck : cert246Data.rhsWeightEncodingCheck certRhsLabelCount certRhsFeatureCount
      certRhsDegreeBound certRhsSourceCs certRhsSourcePmask certRhsCoefficientCs
      certRhsCoefficientPmask certRhsCoefficientWidth certRhsCoefficientMask certRhsWeightCs
      certRhsWeightPmask certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.sigEnc
      cert246Data.labelEnc cert246Data.rhsSourceLocationT cert246Data.coeffMag
      cert246Data.rhsWeightT = true) :
    ∀ feature : Fin certRhsFeatureCount, signedValue (certRhsExpectedWeight feature) =
      (certRhsSourceDigit true feature : ℤ) - certRhsSourceDigit false feature := by
  let source := cert246Data.rhsSourceWeightLanes certRhsLabelCount certRhsDegreeBound
    certRhsSourceCs certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask
    certRhsCoefficientWidth certRhsCoefficientMask laneWidth cert246Data.sigEnc
    cert246Data.labelEnc cert246Data.rhsSourceLocationT cert246Data.coeffMag
  let expected := cert246Data.rhsExpectedWeightLanes certRhsFeatureCount certRhsWeightCs
    certRhsWeightPmask certRhsWeightWidth certRhsWeightMask laneWidth cert246Data.rhsWeightT
  unfold cert246Data.rhsWeightEncodingCheck at hcheck
  change Bool.and' (Nat.blt (source.bound + expected.bound) (2 ^ laneWidth))
      (Nat.beq (source.positive + expected.negative)
        (source.negative + expected.positive)) = true at hcheck
  rw [Bool.and'_eq_and, Bool.and_eq_true] at hcheck
  obtain ⟨hboundRaw, hcodeRaw⟩ := hcheck
  have hbound : source.bound + expected.bound < 2 ^ laneWidth :=
    Nat.blt_eq.mp hboundRaw
  have hcode : source.positive + expected.negative =
      source.negative + expected.positive := Nat.beq_eq.mp hcodeRaw
  have hsource := rhsSourceWeightLabelRangeLanes_sound laneWidth certRhsLabelCount 0
  change source.bound = _ ∧ source.positive = _ ∧ source.negative = _ at hsource
  rcases hsource with ⟨hsourceBound, hsourcePositiveRaw, hsourceNegativeRaw⟩
  have hsourceBound' : source.bound = certRhsSourceBound := by
    simpa only [certRhsSourceBound, Nat.zero_add] using hsourceBound
  have hsourcePositive : source.positive =
      rhsWeightLaneCode (2 ^ laneWidth) (certRhsSourceDigit true) := by
    rw [hsourcePositiveRaw]
    have h := rhsShiftedSum_eq_laneCode certRhsLabelCount (certRhsDegreeBound + 1)
      certRhsFeatureCount laneWidth
      (fun label exponent ↦ (certRhsActive label exponent) &&
        (Nat.beq (certRhsSign label) 0)) certRhsSourceLocation certRhsMagnitude (by
          intro label hlabel exponent hexponent henabled
          rw [Bool.and_eq_true] at henabled
          exact hlocation label hlabel exponent hexponent henabled.1)
    have hdigit :
        (fun feature : Fin certRhsFeatureCount ↦
          ∑ label ∈ Finset.range certRhsLabelCount,
            ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
              if (certRhsActive label exponent = true ∧ certRhsSign label = 0) ∧
                  certRhsSourceLocation label exponent = feature.val then
                certRhsMagnitude label exponent
              else 0) = certRhsSourceDigit true := by
      funext feature
      simp [certRhsSourceDigit, and_assoc]
    rw [← hdigit]
    simpa only [Bool.and_eq_true, Nat.beq_eq, Nat.zero_add] using h
  have hsourceNegative : source.negative =
      rhsWeightLaneCode (2 ^ laneWidth) (certRhsSourceDigit false) := by
    rw [hsourceNegativeRaw]
    have h := rhsShiftedSum_eq_laneCode certRhsLabelCount (certRhsDegreeBound + 1)
      certRhsFeatureCount laneWidth
      (fun label exponent ↦ (certRhsActive label exponent) &&
        (decide (certRhsSign label ≠ 0))) certRhsSourceLocation certRhsMagnitude (by
          intro label hlabel exponent hexponent henabled
          rw [Bool.and_eq_true] at henabled
          exact hlocation label hlabel exponent hexponent henabled.1)
    have hdigit :
        (fun feature : Fin certRhsFeatureCount ↦
          ∑ label ∈ Finset.range certRhsLabelCount,
            ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
              if (certRhsActive label exponent = true ∧ certRhsSign label ≠ 0) ∧
                  certRhsSourceLocation label exponent = feature.val then
                certRhsMagnitude label exponent
              else 0) = certRhsSourceDigit false := by
      funext feature
      simp [certRhsSourceDigit, and_assoc]
    rw [← hdigit]
    simpa only [Bool.and_eq_true, decide_eq_true_eq, Nat.zero_add] using h
  have hexpected := rhsExpectedWeightRangeLanes_sound laneWidth certRhsFeatureCount 0
  change expected.positive = _ ∧ expected.negative = _ ∧ _ at hexpected
  rcases hexpected with ⟨hexpectedPositiveRaw, hexpectedNegativeRaw, hexpectedBound⟩
  have hexpectedPositive : expected.positive =
      rhsWeightLaneCode (2 ^ laneWidth) (certRhsExpectedDigit true) := by
    rw [hexpectedPositiveRaw]
    unfold rhsWeightLaneCode certRhsExpectedDigit
    symm
    let term : ℕ → ℕ := fun index ↦
      (let value := certRhsExpectedWeight index
       if (cert246Data.signedSign value = 0) = (true = true) then
         cert246Data.signedMagnitude value else 0) *
        (2 ^ laneWidth) ^ index
    change (∑ index : Fin certRhsFeatureCount, term index.val) = _
    rw [Fin.sum_univ_eq_sum_range term]
    apply Finset.sum_congr rfl
    intro feature hfeature
    simp only [Nat.zero_add]
    by_cases hsign : cert246Data.signedSign (certRhsExpectedWeight feature) = 0
    · simp [term, hsign, Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_mul]
    · simp [term, hsign]
  have hexpectedNegative : expected.negative =
      rhsWeightLaneCode (2 ^ laneWidth) (certRhsExpectedDigit false) := by
    rw [hexpectedNegativeRaw]
    unfold rhsWeightLaneCode certRhsExpectedDigit
    symm
    let term : ℕ → ℕ := fun index ↦
      (let value := certRhsExpectedWeight index
       if (cert246Data.signedSign value = 0) = (false = true) then
         cert246Data.signedMagnitude value else 0) *
        (2 ^ laneWidth) ^ index
    change (∑ index : Fin certRhsFeatureCount, term index.val) = _
    rw [Fin.sum_univ_eq_sum_range term]
    apply Finset.sum_congr rfl
    intro feature hfeature
    simp only [Nat.zero_add]
    by_cases hsign : cert246Data.signedSign (certRhsExpectedWeight feature) = 0
    · simp [term, hsign]
    · simp [term, hsign, Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_mul]
  have hbalance := rhsWeightLaneBalance_sound (certRhsSourceDigit true)
    (certRhsSourceDigit false) (certRhsExpectedDigit true) (certRhsExpectedDigit false)
    (fun feature ↦ hsourceBound' ▸ certRhsSourceDigit_le_bound true feature)
    (fun feature ↦ hsourceBound' ▸ certRhsSourceDigit_le_bound false feature)
    (fun feature ↦ by
      unfold certRhsExpectedDigit
      have hmagnitude := hexpectedBound feature.val (by omega) (by omega)
      change cert246Data.signedMagnitude (certRhsExpectedWeight feature) ≤ expected.bound
        at hmagnitude
      by_cases hsign : cert246Data.signedSign (certRhsExpectedWeight feature) = 0
      · simpa [hsign] using hmagnitude
      · simp [hsign])
    (fun feature ↦ by
      unfold certRhsExpectedDigit
      have hmagnitude := hexpectedBound feature.val (by omega) (by omega)
      change cert246Data.signedMagnitude (certRhsExpectedWeight feature) ≤ expected.bound
        at hmagnitude
      by_cases hsign : cert246Data.signedSign (certRhsExpectedWeight feature) = 0
      · simp [hsign]
      · simpa [hsign] using hmagnitude)
    hlaneWidth hbound (by
      rw [← hsourcePositive, ← hsourceNegative, ← hexpectedPositive,
        ← hexpectedNegative]
      exact hcode)
  intro feature
  have hdigit := hbalance feature
  rw [← hdigit]
  unfold certRhsExpectedDigit signedValue
  by_cases hsign : cert246Data.signedSign (certRhsExpectedWeight feature) = 0 <;> simp [hsign]

end PrimeGaps.Gap246
