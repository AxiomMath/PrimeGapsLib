/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Certificate.MomentSound
public import PrimeGapsCert.Gap246.LHS.HighLevel


/-! # Concrete soundness for the packed sparse LHS transform -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- The packed member at a valid group offset is the corresponding mathematical member. -/
theorem certLhsMember (group : Fin 138) (offset : Fin (certLhsPartition.group group).size) :
    certLhsPartition.member certLhsPartition_bound group offset =
      let position := (certLhsPartition.group group).start + offset
      ⟨cert246Data.lhsMember cert246Data.lhsMemberEnc position,
        certLhsMembers_lt position
          (lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _)
            (certLhsPartition_bound group))⟩ := by
  apply Fin.ext
  simp only [LhsDegreePartition.member, LhsDegreePartition.flatMember, certLhsPartition,
    Fin.val_mk]
  rw [Nat.mod_eq_of_lt]
  exact certLhsMembers_lt _
    (lt_of_lt_of_le (Nat.add_lt_add_left offset.isLt _) (certLhsPartition_bound group))

/-- The raw coefficient at a group offset is the coefficient in the mathematical certificate. -/
theorem certLhsLabelValue (group : Fin 138)
    (offset : Fin (certLhsPartition.group group).size) :
    lhsLabelValue cert246Data.lhsMemberEnc cert246Data.labelEnc 9 511 128
        (2 ^ 128 - 1) cert246Data.coeffMag
        ((certLhsPartition.group group).start + offset) =
      certLabelCoefficient
        (certLhsPartition.member certLhsPartition_bound group offset) := by
  rw [certLhsMember]
  unfold lhsLabelValue certLabelCoefficient certLabelField
  dsimp only
  have hsign := labelSign_lt_two (cert246Data.labelField cert246Data.labelEnc
    (cert246Data.lhsMember cert246Data.lhsMemberEnc
      ((certLhsPartition.group group).start + offset)))
  by_cases hzero : cert246Data.labelSign (cert246Data.labelField cert246Data.labelEnc
      (cert246Data.lhsMember cert246Data.lhsMemberEnc
        ((certLhsPartition.group group).start + offset))) = 0
  · rw [if_pos hzero, if_neg (by omega)]
  · have hone : cert246Data.labelSign (cert246Data.labelField cert246Data.labelEnc
        (cert246Data.lhsMember cert246Data.lhsMemberEnc
          ((certLhsPartition.group group).start + offset))) = 1 := by omega
    rw [if_neg hzero, if_pos hone]

/-- The raw high-lane lookup is the mathematical top moment lookup. -/
theorem certLhsMomentTop (target signature : Fin 272) :
    cert246Data.lhsMomentTop 7 127 512 (2 ^ 512 - 1) 256 cert246Data.pairT
        target signature =
      certPairValue (signaturePairIndex target signature) / 2 ^ 256 := by
  simp only [cert246Data.lhsMomentTop, certPairValue, signaturePairIndex_divNat,
    signaturePairIndex_modNat]
  exact Nat.shiftRight_eq_div_pow _ _

/-- Concrete direct LHS transform with no dependent certificate fields in its type. -/
noncomputable def certLhsDirectTransform (group : Fin 138) (target : Fin 272) : ℤ :=
  ∑ offset : Fin (certLhsPartition.group group).size,
    certLabelCoefficient (certLhsPartition.member certLhsPartition_bound group offset) *
      ((certPairValue (signaturePairIndex target
        (certLabelSignature
          (certLhsPartition.member certLhsPartition_bound group offset))) / 2 ^ 256 : ℕ) : ℤ)

/-- The mathematical specification of a raw transform is the direct sparse-transform sum. -/
theorem certLhsTransformSpec_eq (group : Fin 138) (target : Fin 272) :
    lhsTransformSpec cert246Data.lhsMemberEnc cert246Data.labelEnc
        cert246Data.lhsGroupEnc 9 511 128 (2 ^ 128 - 1) 7 127 512
        (2 ^ 512 - 1) 256 cert246Data.coeffMag cert246Data.pairT group target =
      certLhsDirectTransform group target := by
  change lhsTransformSpec cert246Data.lhsMemberEnc cert246Data.labelEnc
      cert246Data.lhsGroupEnc 9 511 128 (2 ^ 128 - 1) 7 127 512
        (2 ^ 512 - 1) 256 cert246Data.coeffMag cert246Data.pairT group target =
    ∑ offset : Fin (certLhsPartition.group group).size,
      certLabelCoefficient
          (certLhsPartition.member certLhsPartition_bound group offset) *
        ((certPairValue (signaturePairIndex target
          (certLabelSignature
            (certLhsPartition.member certLhsPartition_bound group offset))) / 2 ^ 256 : ℕ) : ℤ)
  unfold lhsTransformSpec
  change (∑ offset ∈ Finset.range (certLhsPartition.group group).size,
      lhsLabelValue cert246Data.lhsMemberEnc cert246Data.labelEnc 9 511 128
          (2 ^ 128 - 1) cert246Data.coeffMag
          ((certLhsPartition.group group).start + offset) *
        cert246Data.lhsMomentTop 7 127 512 (2 ^ 512 - 1) 256 cert246Data.pairT
          target (cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc
            (cert246Data.lhsMember cert246Data.lhsMemberEnc
              ((certLhsPartition.group group).start + offset)))) = _)
  rw [← Fin.sum_univ_eq_sum_range]
  apply Finset.sum_congr rfl
  intro offset _
  rw [certLhsLabelValue group offset]
  have hsignature : cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc
      (cert246Data.lhsMember cert246Data.lhsMemberEnc
        ((certLhsPartition.group group).start + offset))) =
      (certLabelSignature
        (certLhsPartition.member certLhsPartition_bound group offset)).val := by
    rw [certLhsMember]
    rfl
  rw [hsignature]
  rw [certLhsMomentTop]

/-- Pointwise raw equalities for all stored LHS transform entries. -/
def CertLhsTransformChecks : Prop :=
  ∀ entry < 5533,
    let key := cert246Data.keyField cert246Data.lhsKeyEnc entry
    cert246Data.treeAt 7 127 320 (2 ^ 320 - 1) cert246Data.lhsTransformT entry =
      cert246Data.lhsTransformValue cert246Data.lhsMemberEnc cert246Data.labelEnc
        cert246Data.lhsGroupEnc 9 511 128 (2 ^ 128 - 1) 7 127 512
        (2 ^ 512 - 1) 256 cert246Data.coeffMag cert246Data.pairT
        (cert246Data.keyGroup key) (cert246Data.keyTarget key)

/-- Raw transform checks certify every stored mathematical sparse-transform value. -/
theorem certLhsTransformValues_correct (hchecks : CertLhsTransformChecks) :
    ∀ entry, LhsSparseTransformValueCorrectAt preEpsWitnessInt certLhsPartition
      certLhsPartition_valid certLhsTransformValue certLhsTransformIndex entry := by
  intro entry
  let field := cert246Data.keyField cert246Data.lhsKeyEnc entry
  have hbound := certLhsKeys_bound entry entry.isLt
  let rawGroup : Fin 138 := ⟨cert246Data.keyGroup field, hbound.1⟩
  let rawTarget : Fin 272 := ⟨cert246Data.keyTarget field, hbound.2⟩
  let modGroup : Fin 138 := ⟨cert246Data.keyGroup field % 138, by omega⟩
  let modTarget : Fin 272 := ⟨cert246Data.keyTarget field % 272, by omega⟩
  change signedValue
      (cert246Data.treeAt 7 127 320 (2 ^ 320 - 1) cert246Data.lhsTransformT entry) =
    certLhsDirectTransform modGroup modTarget
  have hgroup : modGroup = rawGroup := by
    exact Fin.ext (Nat.mod_eq_of_lt hbound.1)
  have htarget : modTarget = rawTarget := by
    exact Fin.ext (Nat.mod_eq_of_lt hbound.2)
  rw [hgroup, htarget]
  rw [hchecks entry entry.isLt]
  rw [lhsTransformValue_sound]
  exact certLhsTransformSpec_eq rawGroup rawTarget

/-- All sparse LHS transform lookups are exact once the stored entries are checked. -/
theorem certLhsTransform_correct (hchecks : CertLhsTransformChecks) :
    ∀ group target, LhsDegreeTransformCorrectAt preEpsWitnessInt certLhsPartition
      certLhsPartition_valid certLhsTransform group target := by
  simpa only [certLhsTransform] using
    preEpsWitnessInt.lhsSparseTransformGet_correct certLhsPartition certLhsPartition_valid
      certLhsTransformValue certLhsTransformIndex certLhsTransformIndex_valid
      (certLhsTransformValues_correct hchecks)

/-- A positive raw location reads the same stored value as the mathematical sparse interface. -/
theorem certLhsTransformAt_eq (group target : ℕ) (hgroup : group < 138)
    (htarget : target < 272)
    (hpositive : 0 < cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
      (group * 272 + target)) :
    signedValue (cert246Data.lhsTransformAt 272 12 4095 7 127 320 (2 ^ 320 - 1)
      cert246Data.lhsLocationT cert246Data.lhsTransformT group target) =
      certLhsTransform ⟨group, hgroup⟩ ⟨target, htarget⟩ := by
  let location := cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
    (group * 272 + target)
  have hlocation : location < 5534 := by
    have := certLhsLocations_bound group hgroup target htarget
    omega
  have hne : location ≠ 0 := by omega
  unfold certLhsTransform PreEpsCertificateExplicitDagInt.lhsSparseTransformGet
  change signedValue (cert246Data.treeAt 7 127 320 (2 ^ 320 - 1)
      cert246Data.lhsTransformT (location - 1)) = _
  simp only [certLhsTransformIndex, Fin.val_mk, Nat.mod_eq_of_lt hlocation, hne,
    ↓reduceDIte, LhsSparseTransformIndex.entryOf, certLhsTransformValue, location]

end PrimeGaps.Gap246
