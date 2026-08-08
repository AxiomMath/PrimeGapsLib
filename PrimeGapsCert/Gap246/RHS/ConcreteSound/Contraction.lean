/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Transform
public import PrimeGapsCert.Gap246.Sparse.RhsContractionSound
public import PrimeGapsCert.Gap246.Sparse.RhsFeatureSound

import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic.Positivity.Finset

/-! # Concrete RHS contraction soundness -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- One oriented smaller-side contraction in the concrete mathematical interface. -/
noncomputable def certRhsContractionSide (source transformGroup : Fin 172) : ℤ :=
  ∑ offset : Fin (certRhsPartition.group source).size,
    let feature := certRhsPartition.member certRhsPartition_bound source offset
    (certRhsFeature feature).weight *
      certRhsTransform transformGroup (certRhsFeature feature).signature

/-- The raw oriented contraction is the corresponding mathematical finite sum. -/
theorem certRhsContractionSide_sound (source transformGroup : Fin 172)
    (hsupport : ∀ offset < (certRhsPartition.group source).size,
      let featureField := cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc
        ((certRhsPartition.group source).start + offset)
      let target := cert246Data.rhsFeatureSignature featureField
      0 < cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
        (transformGroup * 272 + target)) :
    (∑ offset ∈ Finset.range (certRhsPartition.group source).size,
      let position := (certRhsPartition.group source).start + offset
      let featureField := cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc position
      let target := cert246Data.rhsFeatureSignature featureField
      rhsFeatureWeight 8 255 256 (2 ^ 256 - 1) cert246Data.rhsWeightT position *
        signedValue (cert246Data.rhsTransformAt 272 12 4095 7 127 384
          (2 ^ 384 - 1) cert246Data.rhsLocationT cert246Data.rhsTransformT
          transformGroup target)) = certRhsContractionSide source transformGroup := by
  unfold certRhsContractionSide
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro offset _
  dsimp only
  rw [certRhsFeatureWeight source offset]
  let feature := certRhsPartition.member certRhsPartition_bound source offset
  let rawTarget := cert246Data.rhsFeatureSignature
    (cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc
      ((certRhsPartition.group source).start + offset))
  have htarget : rawTarget < 272 := by
    have hposition : (certRhsPartition.group source).start + offset < 1504 :=
      lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _) (certRhsPartition_bound source)
    exact certRhsFeatureSignature_bound _ hposition
  have hpositive : 0 < cert246Data.treeAt 12 4095 16 65535
      cert246Data.rhsLocationT (transformGroup * 272 + rawTarget) :=
    hsupport offset offset.isLt
  rw [certRhsTransformAt_eq transformGroup rawTarget transformGroup.isLt htarget hpositive]
  have hsignature : (⟨rawTarget, htarget⟩ : Fin 272) =
      (certRhsFeature feature).signature := by
    apply Fin.ext
    exact (by
      simpa only [rawTarget, feature, certRhsMember] using
        (certRhsFeatureSignature_raw feature).symm)
  rw [hsignature]

/-- Concrete smaller-side RHS contraction, stated without dependent certificate fields. -/
noncomputable def certRhsContraction (left right : Fin 172) : ℤ :=
  Bool.rec (certRhsContractionSide right left) (certRhsContractionSide left right)
    (Nat.ble (certRhsPartition.group left).size (certRhsPartition.group right).size)

/-- The concrete contraction is the abstract certificate contraction. -/
theorem certRhsContraction_eq (left right : Fin 172) :
    certRhsContraction left right =
      preEpsWitnessInt.rhsDegreeContraction certRhsFeature certRhsPartition
        certRhsPartition_valid certRhsTransform left right := by
  unfold certRhsContraction PreEpsCertificateExplicitDagInt.rhsDegreeContraction
  by_cases hsize : (certRhsPartition.group left).size ≤
      (certRhsPartition.group right).size
  · rw [if_pos hsize, show Nat.ble (certRhsPartition.group left).size
      (certRhsPartition.group right).size = true from Nat.ble_eq.mpr hsize]
    rfl
  · have hble : Nat.ble (certRhsPartition.group left).size
        (certRhsPartition.group right).size = false :=
      Bool.eq_false_of_not_eq_true fun htrue ↦ hsize (Nat.ble_eq.mp htrue)
    rw [if_neg hsize, hble]
    rfl

/-- Raw contraction soundness from pointwise positivity of all queried sparse locations. -/
theorem certRhsContractionSpec_eq_of_support (left right : Fin 172)
    (hqueries :
      let leftField := cert246Data.groupField cert246Data.rhsGroupEnc left
      let rightField := cert246Data.groupField cert246Data.rhsGroupEnc right
      let useLeft := Nat.ble (cert246Data.groupSize leftField)
        (cert246Data.groupSize rightField)
      let sourceField : ℕ := Bool.rec rightField leftField useLeft
      let transformGroup : ℕ := Bool.rec left right useLeft
      ∀ offset < cert246Data.groupSize sourceField,
        let featureField := cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc
          (cert246Data.groupStart sourceField + offset)
        let target := cert246Data.rhsFeatureSignature featureField
        0 < cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
          (transformGroup * 272 + target)) :
    rhsContractionSpec 272 cert246Data.rhsFeatureEnc cert246Data.rhsGroupEnc
        12 4095 7 127 384 (2 ^ 384 - 1) 8 255 256 (2 ^ 256 - 1)
        cert246Data.rhsLocationT cert246Data.rhsTransformT cert246Data.rhsWeightT
        left right = certRhsContraction left right := by
  rcases hble : Nat.ble
      (cert246Data.groupSize
        (cert246Data.groupField cert246Data.rhsGroupEnc left))
      (cert246Data.groupSize
        (cert246Data.groupField cert246Data.rhsGroupEnc right)) with _ | _
  · have hside := certRhsContractionSide_sound right left (by
      simpa only [hble, certRhsPartition] using hqueries)
    simpa only [rhsContractionSpec, certRhsContraction, certRhsPartition, hble] using hside
  · have hside := certRhsContractionSide_sound left right (by
      simpa only [hble, certRhsPartition] using hqueries)
    simpa only [rhsContractionSpec, certRhsContraction, certRhsPartition, hble] using hside

/-- Pointwise correctness required of the packed RHS radial-factor table. -/
def CertRhsRadialChecks : Prop :=
  ∀ q e, 49 ≤ q → q + e ≤ 101 →
    cert246Data.treeAt 6 63 832 (2 ^ 832 - 1) cert246Data.rhsRadialT
        (q * 102 + e) = cert246Data.rhsRadialFormula 50 25 q e

/-- A checked radial-table entry is the corresponding direct mathematical factor. -/
theorem certRhsRadial_correct (hchecks : CertRhsRadialChecks) (q e : ℕ)
    (hlower : 49 ≤ q) (hupper : q + e ≤ 101) :
    cert246Data.treeAt 6 63 832 (2 ^ 832 - 1) cert246Data.rhsRadialT
        (q * 102 + e) = certFactorTables.radial q e := by
  rw [hchecks q e hlower hupper, rhsRadialFormula_eq]
  rfl

/-- One concrete pair of RHS degree groups. -/
noncomputable def certRhsPair (left right : Fin 172) : ℤ :=
  let leftGroup := certRhsPartition.group left
  let rightGroup := certRhsPartition.group right
  certFactorTables.radial
      (49 + leftGroup.residualDegree + rightGroup.residualDegree)
      (leftGroup.radialDegree + rightGroup.radialDegree) *
    certRhsContraction left right

/-- The concrete RHS group pair is the corresponding abstract transformed group pair. -/
theorem certRhsPair_eq (left right : Fin 172) :
    certRhsPair left right =
      preEpsWitnessInt.rhsDegreeGroupPairTransformed certFactorTables certRhsFeature
        certRhsPartition certRhsPartition_valid certRhsTransform left right := by
  unfold certRhsPair PreEpsCertificateExplicitDagInt.rhsDegreeGroupPairTransformed
  rw [certRhsContraction_eq]
  dsimp only
  rw [show 50 - 1 = 49 by norm_num]
  rw [Nat.add_assoc]

/-- A concrete RHS pair addressed by a natural group index, or zero out of range. -/
noncomputable def certRhsPairNat (left : Fin 172) (right : ℕ) : ℤ :=
  if hright : right < 172 then certRhsPair left ⟨right, hright⟩ else 0

/-- An in-range natural group index reads the corresponding concrete RHS pair. -/
theorem certRhsPairNat_eq (left : Fin 172) (right : ℕ) (hright : right < 172) :
    certRhsPairNat left right = certRhsPair left ⟨right, hright⟩ := by
  simp only [certRhsPairNat, dif_pos hright]

end PrimeGaps.Gap246
