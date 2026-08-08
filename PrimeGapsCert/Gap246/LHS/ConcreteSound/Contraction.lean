/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.LHS.ConcreteSound.Transform

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

/-! # Concrete soundness for packed sparse LHS contractions -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- One oriented smaller-side contraction in the concrete mathematical interface. -/
noncomputable def certLhsContractionSide (source transformGroup : Fin 138) : ℤ :=
  ∑ offset : Fin (certLhsPartition.group source).size,
    let member := certLhsPartition.member certLhsPartition_bound source offset
    certLabelCoefficient member * certLhsTransform transformGroup (certLabelSignature member)

/-- The raw oriented contraction is the corresponding mathematical finite sum. -/
theorem certLhsContractionSide_sound (source transformGroup : Fin 138)
    (hsupport : ∀ offset < (certLhsPartition.group source).size,
      let label := cert246Data.lhsMember cert246Data.lhsMemberEnc
        ((certLhsPartition.group source).start + offset)
      let target := cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label)
      0 < cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
        (transformGroup * 272 + target)) :
    (∑ offset ∈ Finset.range (certLhsPartition.group source).size,
      let position := (certLhsPartition.group source).start + offset
      let label := cert246Data.lhsMember cert246Data.lhsMemberEnc position
      let target := cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label)
      lhsLabelValue cert246Data.lhsMemberEnc cert246Data.labelEnc 9 511 128
          (2 ^ 128 - 1) cert246Data.coeffMag position *
        signedValue (cert246Data.lhsTransformAt 272 12 4095 7 127 320
          (2 ^ 320 - 1) cert246Data.lhsLocationT cert246Data.lhsTransformT
          transformGroup target)) = certLhsContractionSide source transformGroup := by
  unfold certLhsContractionSide
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro offset _
  dsimp only
  rw [certLhsLabelValue source offset]
  let member := certLhsPartition.member certLhsPartition_bound source offset
  let rawTarget := cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc
    (cert246Data.lhsMember cert246Data.lhsMemberEnc
      ((certLhsPartition.group source).start + offset)))
  have htarget : rawTarget < 272 := by
    let position := (certLhsPartition.group source).start + offset
    have hposition : position < 1295 :=
      lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _) (certLhsPartition_bound source)
    exact (certLabels _ (certLhsMembers_lt position hposition)).1
  have hpositive : 0 < cert246Data.treeAt 12 4095 16 65535
      cert246Data.lhsLocationT (transformGroup * 272 + rawTarget) :=
    hsupport offset offset.isLt
  rw [certLhsTransformAt_eq transformGroup rawTarget transformGroup.isLt htarget hpositive]
  have hsignature : (⟨rawTarget, htarget⟩ : Fin 272) = certLabelSignature member := by
    apply Fin.ext
    unfold rawTarget member certLabelSignature certLabelField
    rw [certLhsMember]
  rw [hsignature]

/-- Concrete smaller-side contraction, stated without dependent certificate fields. -/
noncomputable def certLhsContraction (left right : Fin 138) : ℤ :=
  Bool.rec (certLhsContractionSide right left) (certLhsContractionSide left right)
    (Nat.ble (certLhsPartition.group left).size (certLhsPartition.group right).size)

/-- The concrete contraction is the abstract certificate contraction. -/
theorem certLhsContraction_eq (left right : Fin 138) :
    certLhsContraction left right =
      preEpsWitnessInt.lhsDegreeContraction certLhsPartition certLhsPartition_valid
        certLhsTransform left right := by
  unfold certLhsContraction PreEpsCertificateExplicitDagInt.lhsDegreeContraction
  by_cases hsize : (certLhsPartition.group left).size ≤
      (certLhsPartition.group right).size
  · rw [if_pos hsize, show Nat.ble (certLhsPartition.group left).size
      (certLhsPartition.group right).size = true from Nat.ble_eq.mpr hsize]
    rfl
  · have hble : Nat.ble (certLhsPartition.group left).size
        (certLhsPartition.group right).size = false :=
      Bool.eq_false_of_not_eq_true fun htrue ↦ hsize (Nat.ble_eq.mp htrue)
    rw [if_neg hsize, hble]
    rfl

/-- Raw contraction soundness from pointwise positivity of all queried sparse locations. -/
theorem certLhsContractionSpec_eq_of_support (left right : Fin 138)
    (hqueries :
      let leftField := cert246Data.groupField cert246Data.lhsGroupEnc left
      let rightField := cert246Data.groupField cert246Data.lhsGroupEnc right
      let useLeft := Nat.ble (cert246Data.groupSize leftField)
        (cert246Data.groupSize rightField)
      let sourceField : ℕ := Bool.rec rightField leftField useLeft
      let transformGroup : ℕ := Bool.rec left right useLeft
      ∀ offset < cert246Data.groupSize sourceField,
        let label := cert246Data.lhsMember cert246Data.lhsMemberEnc
          (cert246Data.groupStart sourceField + offset)
        let target := cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label)
        0 < cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
          (transformGroup * 272 + target)) :
    lhsContractionSpec 272 cert246Data.lhsMemberEnc cert246Data.labelEnc
        cert246Data.lhsGroupEnc 12 4095 7 127 320 (2 ^ 320 - 1) 9 511 128
        (2 ^ 128 - 1) cert246Data.lhsLocationT cert246Data.lhsTransformT
        cert246Data.coeffMag left right =
      certLhsContraction left right := by
  rcases hble : Nat.ble
      (cert246Data.groupSize
        (cert246Data.groupField cert246Data.lhsGroupEnc left))
      (cert246Data.groupSize
        (cert246Data.groupField cert246Data.lhsGroupEnc right)) with _ | _
  · have hside := certLhsContractionSide_sound right left (by
      simpa only [hble, certLhsPartition] using hqueries)
    simpa only [lhsContractionSpec, certLhsContraction, certLhsPartition, hble] using hside
  · have hside := certLhsContractionSide_sound left right (by
      simpa only [hble, certLhsPartition] using hqueries)
    simpa only [lhsContractionSpec, certLhsContraction, certLhsPartition, hble] using hside

end PrimeGaps.Gap246
