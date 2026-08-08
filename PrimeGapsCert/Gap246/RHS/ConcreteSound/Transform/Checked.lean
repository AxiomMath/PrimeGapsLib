/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Transform.Direct


/-! # Checked sparse RHS transform soundness -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Pointwise raw equalities for all stored RHS transform entries. -/
def CertRhsTransformChecks : Prop :=
  ∀ entry < 6057,
    let key := cert246Data.keyField cert246Data.rhsKeyEnc entry
    cert246Data.treeAt 7 127 384 (2 ^ 384 - 1) cert246Data.rhsTransformT entry =
      cert246Data.rhsTransformValue cert246Data.rhsFeatureEnc
        cert246Data.rhsGroupEnc 8 255 256 (2 ^ 256 - 1) 7 127 512
        (2 ^ 512 - 1) (2 ^ 256 - 1) cert246Data.rhsWeightT cert246Data.pairT
        (cert246Data.keyGroup key) (cert246Data.keyTarget key)

/-- Raw transform checks certify every stored mathematical sparse-transform value. -/
theorem certRhsTransformValues_correct (hchecks : CertRhsTransformChecks) :
    ∀ entry, RhsSparseTransformValueCorrectAt preEpsWitnessInt certRhsFeature
      certRhsPartition certRhsPartition_valid certRhsTransformValue certRhsTransformIndex
        entry := by
  intro entry
  let field := cert246Data.keyField cert246Data.rhsKeyEnc entry
  have hbound := certRhsKeys_bound entry entry.isLt
  let rawGroup : Fin 172 := ⟨cert246Data.keyGroup field, hbound.1⟩
  let rawTarget : Fin 272 := ⟨cert246Data.keyTarget field, hbound.2⟩
  let modGroup : Fin 172 := ⟨cert246Data.keyGroup field % 172, by omega⟩
  let modTarget : Fin 272 := ⟨cert246Data.keyTarget field % 272, by omega⟩
  change signedValue
      (cert246Data.treeAt 7 127 384 (2 ^ 384 - 1) cert246Data.rhsTransformT entry) =
    certRhsDirectTransform modGroup modTarget
  have hgroup : modGroup = rawGroup := by
    exact Fin.ext (Nat.mod_eq_of_lt hbound.1)
  have htarget : modTarget = rawTarget := by
    exact Fin.ext (Nat.mod_eq_of_lt hbound.2)
  rw [hgroup, htarget]
  rw [hchecks entry entry.isLt]
  rw [rhsTransformValue_sound]
  exact certRhsTransformSpec_eq rawGroup rawTarget

/-- All sparse RHS transform lookups are exact once the stored entries are checked. -/
theorem certRhsTransform_correct (hchecks : CertRhsTransformChecks) :
    ∀ group target, RhsDegreeTransformCorrectAt preEpsWitnessInt certRhsFeature
      certRhsPartition certRhsPartition_valid certRhsTransform group target := by
  simpa only [certRhsTransform] using
    preEpsWitnessInt.rhsSparseTransformGet_correct certRhsFeature certRhsPartition
      certRhsPartition_valid certRhsTransformValue certRhsTransformIndex
      certRhsTransformIndex_valid (certRhsTransformValues_correct hchecks)

/-- A positive raw location reads the same stored value as the mathematical sparse interface. -/
theorem certRhsTransformAt_eq (group target : ℕ) (hgroup : group < 172)
    (htarget : target < 272)
    (hpositive : 0 < cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
      (group * 272 + target)) :
    signedValue (cert246Data.rhsTransformAt 272 12 4095 7 127 384 (2 ^ 384 - 1)
      cert246Data.rhsLocationT cert246Data.rhsTransformT group target) =
      certRhsTransform ⟨group, hgroup⟩ ⟨target, htarget⟩ := by
  let location := cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
    (group * 272 + target)
  have hlocation : location < 6058 := by
    have := certRhsLocations_bound group hgroup target htarget
    omega
  have hne : location ≠ 0 := by omega
  unfold certRhsTransform PreEpsCertificateExplicitDagInt.rhsSparseTransformGet
  change signedValue (cert246Data.treeAt 7 127 384 (2 ^ 384 - 1)
      cert246Data.rhsTransformT (location - 1)) = _
  simp only [certRhsTransformIndex, Fin.val_mk, Nat.mod_eq_of_lt hlocation, hne,
    ↓reduceDIte, LhsSparseTransformIndex.entryOf, certRhsTransformValue, location]

end PrimeGaps.Gap246
