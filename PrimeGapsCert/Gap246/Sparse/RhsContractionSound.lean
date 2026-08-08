/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.RhsTransformSound


/-! # Soundness of sparse RHS contractions -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Mathematical integer sum represented by one raw RHS group contraction. -/
noncomputable def rhsContractionSpec
    (signatureCount featureEnc groupEnc locationCs locationPmask transformCs transformPmask
      transformWidth transformMask weightCs weightPmask weightWidth weightMask : ℕ)
    (locationTree transformTree weightTree : Lean.RArray ℕ) (left right : ℕ) : ℤ :=
  let leftField := cert246Data.groupField groupEnc left
  let rightField := cert246Data.groupField groupEnc right
  let useLeft := Nat.ble (cert246Data.groupSize leftField)
    (cert246Data.groupSize rightField)
  let sourceField : ℕ := Bool.rec rightField leftField useLeft
  let transformGroup : ℕ := Bool.rec left right useLeft
  ∑ offset ∈ Finset.range (cert246Data.groupSize sourceField),
    let position := cert246Data.groupStart sourceField + offset
    let featureField := cert246Data.rhsFeatureField featureEnc position
    rhsFeatureWeight weightCs weightPmask weightWidth weightMask weightTree position *
      signedValue (cert246Data.rhsTransformAt signatureCount locationCs locationPmask
        transformCs transformPmask transformWidth transformMask locationTree transformTree
        transformGroup (cert246Data.rhsFeatureSignature featureField))

/-- The raw two-lane RHS contraction denotes its integer finite sum. -/
theorem rhsContractionValue_sound
    (signatureCount featureEnc groupEnc locationCs locationPmask transformCs transformPmask
      transformWidth transformMask weightCs weightPmask weightWidth weightMask : ℕ)
    (locationTree transformTree weightTree : Lean.RArray ℕ) (left right : ℕ) :
    signedValue (cert246Data.rhsContractionValue signatureCount featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask weightCs weightPmask
      weightWidth weightMask locationTree transformTree weightTree left right) =
      rhsContractionSpec signatureCount featureEnc groupEnc locationCs locationPmask transformCs
        transformPmask transformWidth transformMask weightCs weightPmask weightWidth weightMask
        locationTree transformTree weightTree left right := by
  unfold cert246Data.rhsContractionValue rhsContractionSpec
  let leftField := cert246Data.groupField groupEnc left
  let rightField := cert246Data.groupField groupEnc right
  let useLeft := Nat.ble (cert246Data.groupSize leftField)
    (cert246Data.groupSize rightField)
  let sourceField : ℕ := Bool.rec rightField leftField useLeft
  let transformGroup : ℕ := Bool.rec left right useLeft
  let weight : ℕ → ℕ := fun cursor ↦
    cert246Data.treeAt weightCs weightPmask weightWidth weightMask weightTree cursor
  let transform : ℕ → ℕ := fun cursor ↦
    let featureField := cert246Data.rhsFeatureField featureEnc cursor
    cert246Data.rhsTransformAt signatureCount locationCs locationPmask transformCs
      transformPmask transformWidth transformMask locationTree transformTree transformGroup
      (cert246Data.rhsFeatureSignature featureField)
  simp only [Nat.add_eq, Nat.mul_eq]
  rw [signedRec_sound
    (fun cursor ↦ Nat.beq (cert246Data.signedSign (weight cursor))
      (cert246Data.signedSign (transform cursor)))
    (fun cursor ↦ cert246Data.signedMagnitude (weight cursor) *
      cert246Data.signedMagnitude (transform cursor))]
  simp only [Int.ofNat_zero, sub_self, zero_add]
  apply Finset.sum_congr rfl
  intro offset _
  unfold weight transform rhsFeatureWeight
  simp only [Nat.beq_eq]
  exact signedProductTerm _ _

end PrimeGaps.Gap246
