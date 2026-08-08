/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.RhsContractionSound

import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum.Abs
import Mathlib.Tactic.NormNum.DivMod
import Mathlib.Tactic.NormNum.OfScientific
import Mathlib.Tactic.Ring.RingNF

/-! # Soundness of sparse RHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Mathematical integer sum represented by one raw RHS row. -/
noncomputable def rhsRowSpec
    (dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask weightCs weightPmask
      weightWidth weightMask radialCs radialPmask radialWidth radialMask : ℕ)
    (locationTree transformTree weightTree radialTree : Lean.RArray ℕ) (left : ℕ) : ℤ :=
  let leftField := cert246Data.groupField groupEnc left
  ∑ offset ∈ Finset.range (groupCount - left),
    let right := left + offset
    let rightField := cert246Data.groupField groupEnc right
    let q := dimension - 1 + cert246Data.groupLowDegree leftField +
      cert246Data.groupLowDegree rightField
    let e := cert246Data.groupHighDegree leftField + cert246Data.groupHighDegree rightField
    let radial := cert246Data.treeAt radialCs radialPmask radialWidth radialMask radialTree
      (q * radialDimension + e)
    let factor := Bool.rec radial (2 * radial) (Nat.blt left right)
    factor * rhsContractionSpec signatureCount featureEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask weightCs weightPmask weightWidth
      weightMask locationTree transformTree weightTree left right

/-- The raw two-lane RHS row denotes its integer finite sum. -/
theorem rhsRowValue_sound
    (dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask weightCs weightPmask
      weightWidth weightMask radialCs radialPmask radialWidth radialMask : ℕ)
    (locationTree transformTree weightTree radialTree : Lean.RArray ℕ) (left : ℕ) :
    signedValue (cert246Data.rhsRowValue dimension groupCount signatureCount radialDimension
      featureEnc groupEnc locationCs locationPmask transformCs transformPmask transformWidth
      transformMask weightCs weightPmask weightWidth weightMask radialCs radialPmask radialWidth
      radialMask locationTree transformTree weightTree radialTree left) =
      rhsRowSpec dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
        locationPmask transformCs transformPmask transformWidth transformMask weightCs weightPmask
        weightWidth weightMask radialCs radialPmask radialWidth radialMask locationTree
        transformTree weightTree radialTree left := by
  unfold cert246Data.rhsRowValue rhsRowSpec
  let leftField := cert246Data.groupField groupEnc left
  let contraction : ℕ → ℕ := fun right ↦
    cert246Data.rhsContractionValue signatureCount featureEnc groupEnc locationCs locationPmask
      transformCs transformPmask transformWidth transformMask weightCs weightPmask weightWidth
      weightMask locationTree transformTree weightTree left right
  let factor : ℕ → ℕ := fun right ↦
    let rightField := cert246Data.groupField groupEnc right
    let q := dimension - 1 + cert246Data.groupLowDegree leftField +
      cert246Data.groupLowDegree rightField
    let e := cert246Data.groupHighDegree leftField + cert246Data.groupHighDegree rightField
    let radial := cert246Data.treeAt radialCs radialPmask radialWidth radialMask radialTree
      (q * radialDimension + e)
    Bool.rec radial (2 * radial) (Nat.blt left right)
  simp only [Nat.add_eq, Nat.mul_eq, Nat.sub_eq]
  rw [signedRec_sound
    (fun right ↦ Nat.beq (cert246Data.signedSign (contraction right)) 0)
    (fun right ↦ factor right * cert246Data.signedMagnitude (contraction right))]
  simp only [Int.ofNat_zero, sub_self, zero_add]
  apply Finset.sum_congr rfl
  intro offset _
  let value := contraction (left + offset)
  have hterm :
      (if cert246Data.signedSign value = 0 then
          ((factor (left + offset) * cert246Data.signedMagnitude value : ℕ) : ℤ)
        else -((factor (left + offset) * cert246Data.signedMagnitude value : ℕ) : ℤ)) =
        Int.ofNat (factor (left + offset)) * signedValue value :=
    calc
      _ = if cert246Data.signedSign value = 0 then
            ((cert246Data.signedMagnitude value * factor (left + offset) : ℕ) : ℤ)
          else -((cert246Data.signedMagnitude value * factor (left + offset) : ℕ) : ℤ) := by
        split <;> rw [Nat.mul_comm]
      _ = signedValue value * Int.ofNat (factor (left + offset)) :=
        signedScaleTermNat value (factor (left + offset))
      _ = _ := by ring
  simp only [Nat.beq_eq]
  rw [hterm]
  have hcontraction := rhsContractionValue_sound signatureCount featureEnc groupEnc locationCs
    locationPmask transformCs transformPmask transformWidth transformMask weightCs weightPmask
    weightWidth weightMask locationTree transformTree weightTree left (left + offset)
  change signedValue value = _ at hcontraction
  rw [hcontraction]
  unfold factor
  rcases hfactor : Nat.blt left (left + offset) with _ | _ <;> norm_num [leftField]

private theorem rhsRowCheck_entry
    {dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth
      rowMask weightCs weightPmask weightWidth weightMask radialCs radialPmask radialWidth
      radialMask lower upper : ℕ}
    {locationTree transformTree rowTree weightTree radialTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsRowCheck dimension groupCount signatureCount radialDimension
      featureEnc groupEnc locationCs locationPmask transformCs transformPmask transformWidth
      transformMask rowCs rowPmask rowWidth rowMask weightCs weightPmask weightWidth weightMask
      radialCs radialPmask radialWidth radialMask locationTree transformTree rowTree weightTree
      radialTree lower upper = true) :
    ∀ left, lower ≤ left → left < upper →
      ((Nat.beq (cert246Data.treeAt rowCs rowPmask rowWidth rowMask rowTree left)
          (cert246Data.rhsRowValue dimension groupCount signatureCount radialDimension featureEnc
            groupEnc locationCs locationPmask transformCs transformPmask transformWidth
            transformMask weightCs weightPmask weightWidth weightMask radialCs radialPmask
            radialWidth radialMask locationTree transformTree weightTree radialTree left))
        && (cert246Data.rhsSupportRowCheck groupCount signatureCount featureEnc groupEnc locationCs
          locationPmask locationTree left)) = true := by
  intro left hlower hupper
  unfold cert246Data.rhsRowCheck at hcheck
  exact boolRec_sound _ (upper - lower) lower hcheck left hlower (by omega)

/-- A successful RHS row-range check yields every stored equality in that range. -/
theorem rhsRowCheck_sound
    {dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth
      rowMask weightCs weightPmask weightWidth weightMask radialCs radialPmask radialWidth
      radialMask lower upper : ℕ}
    {locationTree transformTree rowTree weightTree radialTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsRowCheck dimension groupCount signatureCount radialDimension
      featureEnc groupEnc locationCs locationPmask transformCs transformPmask transformWidth
      transformMask rowCs rowPmask rowWidth rowMask weightCs weightPmask weightWidth weightMask
      radialCs radialPmask radialWidth radialMask locationTree transformTree rowTree weightTree
      radialTree lower upper = true) :
    ∀ left, lower ≤ left → left < upper →
      cert246Data.treeAt rowCs rowPmask rowWidth rowMask rowTree left =
        cert246Data.rhsRowValue dimension groupCount signatureCount radialDimension featureEnc
          groupEnc locationCs locationPmask transformCs transformPmask transformWidth transformMask
          weightCs weightPmask weightWidth weightMask radialCs radialPmask radialWidth radialMask
          locationTree transformTree weightTree radialTree left := by
  intro left hlower hupper
  exact Nat.beq_eq.mp (Bool.and_eq_true_iff.mp
    (rhsRowCheck_entry hcheck left hlower hupper)).1

/-- A successful RHS row-range check validates every sparse query made by those rows. -/
theorem rhsRowCheck_support_sound
    {dimension groupCount signatureCount radialDimension featureEnc groupEnc locationCs
      locationPmask transformCs transformPmask transformWidth transformMask rowCs rowPmask rowWidth
      rowMask weightCs weightPmask weightWidth weightMask radialCs radialPmask radialWidth
      radialMask lower upper : ℕ}
    {locationTree transformTree rowTree weightTree radialTree : Lean.RArray ℕ}
    (hcheck : cert246Data.rhsRowCheck dimension groupCount signatureCount radialDimension
      featureEnc groupEnc locationCs locationPmask transformCs transformPmask transformWidth
      transformMask rowCs rowPmask rowWidth rowMask weightCs weightPmask weightWidth weightMask
      radialCs radialPmask radialWidth radialMask locationTree transformTree rowTree weightTree
      radialTree lower upper = true) :
    ∀ left, lower ≤ left → left < upper →
      cert246Data.rhsSupportRowCheck groupCount signatureCount featureEnc groupEnc locationCs
        locationPmask locationTree left = true := fun left hlower hupper ↦
  (Bool.and_eq_true_iff.mp (rhsRowCheck_entry hcheck left hlower hupper)).2

end PrimeGaps.Gap246
