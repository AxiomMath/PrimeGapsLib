/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.Data.Generated
public import PrimeGapsCert.Gap246.Sparse.RhsFeatureSound

import Mathlib.Data.List.Indexes
import Mathlib.Data.Nat.Digits.Lemmas

/-! # Shared definitions for carry-free packed RHS weight soundness -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

open Finset

/-- Polynomial code of fixed-width natural digits. -/
noncomputable def rhsWeightLaneCode {count : ℕ} (base : ℕ) (digit : Fin count → ℕ) : ℕ :=
  ∑ index, digit index * base ^ index.val

private theorem rhsWeightLaneCode_add {count base : ℕ} (left right : Fin count → ℕ) :
    rhsWeightLaneCode base (fun index ↦ left index + right index) =
      rhsWeightLaneCode base left + rhsWeightLaneCode base right := by
  unfold rhsWeightLaneCode
  simp_rw [add_mul]
  exact Finset.sum_add_distrib

private theorem rhsWeightLaneCode_eq_ofDigits {count base : ℕ} (digit : Fin count → ℕ) :
    rhsWeightLaneCode base digit = Nat.ofDigits base (List.ofFn digit) := by
  rw [Nat.ofDigits_eq_sum_mapIdx]
  simp only [List.mapIdx_eq_ofFn, List.get_ofFn, List.length_ofFn, Fin.val_cast,
    List.sum_ofFn]
  rfl

private theorem rhsWeightLaneCode_injective {count base : ℕ} (left right : Fin count → ℕ)
    (hbase : 1 < base) (hleft : ∀ index, left index < base)
    (hright : ∀ index, right index < base)
    (hcode : rhsWeightLaneCode base left = rhsWeightLaneCode base right) : left = right := by
  have hdigits : List.ofFn left = List.ofFn right := by
    apply Nat.ofDigits_inj_of_len_eq hbase
    · simp
    · intro digit hdigit
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hdigit
      exact hleft index
    · intro digit hdigit
      obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hdigit
      exact hright index
    · rw [← rhsWeightLaneCode_eq_ofDigits, ← rhsWeightLaneCode_eq_ofDigits]
      exact hcode
  exact List.ofFn_inj.mp hdigits

/-- A carry-free equality of whole packed lanes implies every signed digit equality. -/
theorem rhsWeightLaneBalance_sound {count laneWidth sourceBound expectedBound : ℕ}
    (sourcePositive sourceNegative expectedPositive expectedNegative : Fin count → ℕ)
    (hsourcePositive : ∀ index, sourcePositive index ≤ sourceBound)
    (hsourceNegative : ∀ index, sourceNegative index ≤ sourceBound)
    (hexpectedPositive : ∀ index, expectedPositive index ≤ expectedBound)
    (hexpectedNegative : ∀ index, expectedNegative index ≤ expectedBound)
    (hlaneWidth : 0 < laneWidth)
    (hbound : sourceBound + expectedBound < 2 ^ laneWidth)
    (hcode : rhsWeightLaneCode (2 ^ laneWidth) sourcePositive +
        rhsWeightLaneCode (2 ^ laneWidth) expectedNegative =
      rhsWeightLaneCode (2 ^ laneWidth) sourceNegative +
        rhsWeightLaneCode (2 ^ laneWidth) expectedPositive) :
    ∀ index, (expectedPositive index : ℤ) - expectedNegative index =
      (sourcePositive index : ℤ) - sourceNegative index := by
  have hbase : 1 < 2 ^ laneWidth :=
    one_lt_pow₀ (by norm_num) (Nat.ne_of_gt hlaneWidth)
  have hdigits := rhsWeightLaneCode_injective
    (fun index ↦ sourcePositive index + expectedNegative index)
    (fun index ↦ sourceNegative index + expectedPositive index) hbase
    (fun index ↦ lt_of_le_of_lt
      (Nat.add_le_add (hsourcePositive index) (hexpectedNegative index)) hbound)
    (fun index ↦ lt_of_le_of_lt
      (Nat.add_le_add (hsourceNegative index) (hexpectedPositive index)) hbound)
    (by simpa only [rhsWeightLaneCode_add] using hcode)
  intro index
  have hdigit := congrFun hdigits index
  have hdigitInteger :
      (sourcePositive index : ℤ) + expectedNegative index =
        sourceNegative index + expectedPositive index := by
    exact_mod_cast hdigit
  omega

/-- Number of source labels scanned by the global RHS feature-weight check. -/
def certRhsLabelCount : ℕ := 1295

/-- Number of stored marginal features scanned by the global RHS feature-weight check. -/
def certRhsFeatureCount : ℕ := 1504

/-- Largest exponent carried by one source label. -/
def certRhsDegreeBound : ℕ := 25

/-- Chunk shift of the packed source-location table. -/
def certRhsSourceCs : ℕ := 10

/-- Chunk mask of the packed source-location table. -/
def certRhsSourcePmask : ℕ := 1023

/-- Chunk shift of the packed coefficient-magnitude table. -/
def certRhsCoefficientCs : ℕ := 9

/-- Chunk mask of the packed coefficient-magnitude table. -/
def certRhsCoefficientPmask : ℕ := 511

/-- Entry width of the packed coefficient-magnitude table. -/
def certRhsCoefficientWidth : ℕ := 128

/-- Entry mask of the packed coefficient-magnitude table. -/
def certRhsCoefficientMask : ℕ := 2 ^ 128 - 1

/-- Chunk shift of the packed feature-weight table. -/
def certRhsWeightCs : ℕ := 8

/-- Chunk mask of the packed feature-weight table. -/
def certRhsWeightPmask : ℕ := 255

/-- Entry width of the packed feature-weight table. -/
def certRhsWeightWidth : ℕ := 256

/-- Entry mask of the packed feature-weight table. -/
def certRhsWeightMask : ℕ := 2 ^ 256 - 1

/-- Packed descriptor of one source label. -/
noncomputable def certRhsLabelField (label : ℕ) : ℕ :=
  cert246Data.labelField cert246Data.labelEnc label

/-- Packed signature descriptor selected by one source label. -/
noncomputable def certRhsSignatureField (label : ℕ) : ℕ :=
  cert246Data.sigField cert246Data.sigEnc (cert246Data.labelSignature (certRhsLabelField label))

/-- Whether one bounded exponent represents a canonical transition of a source label. -/
noncomputable def certRhsActive (label exponent : ℕ) : Bool :=
  cert246Data.rhsSignatureHasExponent (certRhsSignatureField label) exponent

/-- Packed feature location of one bounded source transition. -/
noncomputable def certRhsSourceLocation (label exponent : ℕ) : ℕ :=
  cert246Data.treeAt certRhsSourceCs certRhsSourcePmask 16 65535
    cert246Data.rhsSourceLocationT (label * (certRhsDegreeBound + 1) + exponent)

/-- Unsigned magnitude of one bounded source transition. -/
noncomputable def certRhsMagnitude (label exponent : ℕ) : ℕ :=
  cert246Data.treeAt certRhsCoefficientCs certRhsCoefficientPmask certRhsCoefficientWidth
      certRhsCoefficientMask cert246Data.coeffMag label * exponent ! *
    (cert246Data.labelA (certRhsLabelField label)) ! *
      Nat.descFactorial (certRhsDegreeBound + 1)
        (certRhsDegreeBound - (cert246Data.labelA (certRhsLabelField label) + exponent))

/-- Sign bit of every transition arising from one source label. -/
noncomputable def certRhsSign (label : ℕ) : ℕ :=
  cert246Data.labelSign (certRhsLabelField label)

/-- One stored packed feature weight. -/
noncomputable def certRhsExpectedWeight (feature : ℕ) : ℕ :=
  cert246Data.treeAt certRhsWeightCs certRhsWeightPmask certRhsWeightWidth certRhsWeightMask
    cert246Data.rhsWeightT feature

/-- Total magnitude of every active source transition. -/
noncomputable def certRhsSourceBound : ℕ :=
  ∑ label ∈ Finset.range certRhsLabelCount,
    ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
      if certRhsActive label exponent = true then certRhsMagnitude label exponent else 0

/-- Positive or negative source magnitude accumulated at one feature location. -/
noncomputable def certRhsSourceDigit (positive : Bool) (feature : Fin certRhsFeatureCount) : ℕ :=
  ∑ label ∈ Finset.range certRhsLabelCount,
    ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
      if certRhsActive label exponent = true ∧
          (certRhsSign label = 0) = (positive = true) ∧
          certRhsSourceLocation label exponent = feature.val then
        certRhsMagnitude label exponent
      else 0

/-- Positive or negative magnitude of one proposed stored feature weight. -/
noncomputable def certRhsExpectedDigit (positive : Bool)
    (feature : Fin certRhsFeatureCount) : ℕ :=
  let value := certRhsExpectedWeight feature
  if (cert246Data.signedSign value = 0) = (positive = true) then
    cert246Data.signedMagnitude value
  else 0

/-- The raw checkpoint comparison for one source-label block. -/
noncomputable def certRhsSourceCheckpointBlockCheck (laneWidth blockSize block : ℕ)
    (bound positive negative : Lean.RArray ℕ) : Bool :=
  cert246Data.rhsSourceWeightCheckpointBlockCheck certRhsLabelCount certRhsDegreeBound
    certRhsSourceCs certRhsSourcePmask certRhsCoefficientCs certRhsCoefficientPmask
    certRhsCoefficientWidth certRhsCoefficientMask laneWidth cert246Data.sigEnc
    cert246Data.labelEnc blockSize block cert246Data.rhsSourceLocationT cert246Data.coeffMag
    bound positive negative

/-- The raw checkpoint comparison for one stored-feature block. -/
noncomputable def certRhsExpectedCheckpointBlockCheck (laneWidth blockSize block : ℕ)
    (bound positive negative : Lean.RArray ℕ) : Bool :=
  cert246Data.rhsExpectedWeightCheckpointBlockCheck certRhsFeatureCount certRhsWeightCs
    certRhsWeightPmask certRhsWeightWidth certRhsWeightMask laneWidth blockSize block
    cert246Data.rhsWeightT bound positive negative

private theorem rhsSignaturePositionScan_sound (signatureField exponent : ℕ) :
    ∀ count cursor,
      Nat.rec (motive := fun _ ↦ ℕ → Bool)
          (fun _ ↦ false)
          (fun _ inductionHypothesis position ↦
            (Nat.beq (2 * cert246Data.sigNib signatureField position) exponent) ||
              (inductionHypothesis position.succ))
          count cursor = true ↔
        ∃ position, cursor ≤ position ∧ position < cursor + count ∧
          2 * cert246Data.sigNib signatureField position = exponent := by
  intro count
  induction count with
  | zero =>
      intro cursor
      simp only [Nat.rec_zero, Bool.false_eq_true, false_iff]
      rintro ⟨position, hlower, hupper, _⟩
      omega
  | succ count inductionHypothesis =>
      intro cursor
      simp only [Bool.or_eq_true, Nat.beq_eq, inductionHypothesis cursor.succ]
      constructor
      · rintro (hvalue | ⟨position, hlower, hupper, hvalue⟩)
        · exact ⟨cursor, le_rfl, by omega, hvalue⟩
        · exact ⟨position, by omega, by omega, hvalue⟩
      · rintro ⟨position, hlower, hupper, hvalue⟩
        rcases Nat.eq_or_lt_of_le hlower with rfl | hlower
        · exact Or.inl hvalue
        · exact Or.inr ⟨position, by omega, by omega, hvalue⟩

/-- The bounded raw signature scan recognizes precisely the identity exponent or one stored
signature position. -/
theorem rhsSignatureHasExponent_sound (signatureField exponent : ℕ) :
    cert246Data.rhsSignatureHasExponent signatureField exponent = true ↔
      exponent = 0 ∨ ∃ position < cert246Data.sigCount signatureField,
        2 * cert246Data.sigNib signatureField position = exponent := by
  unfold cert246Data.rhsSignatureHasExponent
  simp only [Bool.or'_eq_or, Nat.mul_eq]
  rw [Bool.or_eq_true, Nat.beq_eq, rhsSignaturePositionScan_sound]
  simp only [Nat.zero_le, zero_add, true_and]

end PrimeGaps.Gap246
