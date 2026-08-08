/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Certificate.Defs
public import PrimeGapsCert.Gap246.LHS.Defs
public import PrimeGapsCert.Gap246.Sparse.LhsSound
import PrimeGapsCert.Gap246.LHS.Checks.Index
import PrimeGapsCert.Meta.Batched

/-! # Mathematical interface to the packed sparse LHS data -/

set_option maxRecDepth 100000

@[expose] public section

namespace PrimeGaps.Gap246

/-- The consecutive partition of basis labels into fixed-degree classes. -/
noncomputable def certLhsPartition : LhsDegreePartition 1295 138 :=
  {
    group := fun group ↦
      let field := cert246Data.groupField cert246Data.lhsGroupEnc group
      {
        start := cert246Data.groupStart field
        size := cert246Data.groupSize field
        distinguishedDegree := cert246Data.groupLowDegree field
        signatureDegree := cert246Data.groupHighDegree field
      }
    memberIndex := fun position ↦
      ⟨cert246Data.lhsMember cert246Data.lhsMemberEnc position % 1295, by omega⟩
    locateGroup := fun label ↦
      let field := cert246Data.inverseField cert246Data.lhsInverseEnc label
      ⟨cert246Data.inverseGroup field % 138, by omega⟩
    locateOffset := fun label ↦
      cert246Data.inverseOffset
        (cert246Data.inverseField cert246Data.lhsInverseEnc label)
  }

/-- Every packed LHS group lies inside the flattened member permutation. -/
theorem certLhsPartition_bound : ∀ group,
    (certLhsPartition.group group).start + (certLhsPartition.group group).size ≤ 1295 := by
  decide +kernel

/-- Every flattened LHS member is an in-range basis label. -/
theorem certLhsMembers_lt : ∀ position < 1295,
    cert246Data.lhsMember cert246Data.lhsMemberEnc position < 1295 := by
  decide +kernel

/-- The generated LHS degree classes form a degree-preserving permutation of the basis. -/
theorem certLhsPartition_valid : certLhsPartition.Valid preEpsWitnessInt := by
  have hkey : ∀ group (offset : Fin (certLhsPartition.group group).size),
      let member := certLhsPartition.member certLhsPartition_bound group offset
      certLabelA member = (certLhsPartition.group group).distinguishedDegree ∧
        cert246Data.labelDegree (certLabelField member) =
          (certLhsPartition.group group).signatureDegree := by
    decide +kernel
  refine { bound := ?_, locateOffset_lt := ?_, right_inv := ?_, left_inv := ?_, key := ?_ }
  · exact certLhsPartition_bound
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · intro group offset
    have h := hkey group offset
    dsimp only at h
    refine ⟨h.1, ?_⟩
    let member := certLhsPartition.member certLhsPartition_bound group offset
    change (certSig (cert246Data.labelSignature (certLabelField member))).sum = _
    calc
      (certSig (cert246Data.labelSignature (certLabelField member))).sum =
          cert246Data.labelDegree (certLabelField member) := by
        rw [certSig_sum]
        simpa only [certLabelField] using (certLabels member member.isLt).2.1.symm
      _ = (certLhsPartition.group group).signatureDegree := h.2

/-- Each LHS group's two recorded degree coordinates fit the certificate degree bound. -/
theorem certLhsGroupDegree_bound : ∀ group < 138,
    let field := cert246Data.groupField cert246Data.lhsGroupEnc group
    cert246Data.groupLowDegree field + cert246Data.groupHighDegree field ≤ 25 := by
  decide +kernel

/-- One externally stored sparse LHS-transform value. -/
noncomputable def certLhsTransformValue (entry : Fin 5533) : ℤ :=
  signedValue (cert246Data.treeAt 7 127 320 (2 ^ 320 - 1)
    cert246Data.lhsTransformT entry)

/-- Sparse locations and keys for the LHS transform. -/
noncomputable def certLhsTransformIndex : LhsSparseTransformIndex 138 272 5533 :=
  {
    location := fun group target ↦
      ⟨cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
        (group * 272 + target) % 5534, by omega⟩
    entryGroup := fun entry ↦
      ⟨cert246Data.keyGroup
        (cert246Data.keyField cert246Data.lhsKeyEnc entry) % 138, by omega⟩
    entryTarget := fun entry ↦
      ⟨cert246Data.keyTarget
        (cert246Data.keyField cert246Data.lhsKeyEnc entry) % 272, by omega⟩
  }

/-- Every nonzero sparse LHS location is bounded and decodes to its queried key. -/
theorem certLhsLocationIndex : ∀ group < 138, ∀ target < 272,
    let location := cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
      (group * 272 + target)
    location = 0 ∨
      (0 < location ∧ location ≤ 5533 ∧
        cert246Data.keyGroup
            (cert246Data.keyField cert246Data.lhsKeyEnc (location - 1)) = group ∧
          cert246Data.keyTarget
            (cert246Data.keyField cert246Data.lhsKeyEnc (location - 1)) = target) := by
  have hblocks : ∀ block : Fin 18, CertLhsLocationBlockCorrect block :=
    combine_batched_theorems% CertLhsLocationBlockCorrect 18
  intro group hgroup target htarget
  let block : Fin 18 := ⟨group / 8, by omega⟩
  apply lhsLocationIndexRangeCheck_sound (hblocks block) group
  · dsimp only [block]
    exact Nat.div_mul_le_self group 8
  · dsimp only [block]
    omega
  · exact htarget

/-- Every positive sparse LHS location points back to its group and target. -/
theorem certLhsTransformIndex_valid : certLhsTransformIndex.Valid := by
  refine { right_inv := ?_ }
  intro group target
  let location := cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
    (group * 272 + target)
  have hindex := certLhsLocationIndex group group.isLt target target.isLt
  change location = 0 ∨
    (0 < location ∧ location ≤ 5533 ∧
      cert246Data.keyGroup
          (cert246Data.keyField cert246Data.lhsKeyEnc (location - 1)) = group ∧
        cert246Data.keyTarget
          (cert246Data.keyField cert246Data.lhsKeyEnc (location - 1)) = target) at hindex
  change if h : location % 5534 = 0 then True else
    (⟨cert246Data.keyGroup
        (cert246Data.keyField cert246Data.lhsKeyEnc (location % 5534 - 1)) % 138,
        by omega⟩ : Fin 138) = group ∧
      (⟨cert246Data.keyTarget
        (cert246Data.keyField cert246Data.lhsKeyEnc (location % 5534 - 1)) % 272,
        by omega⟩ : Fin 272) = target
  rcases hindex with hzero | hpositive
  · simp only [hzero, Nat.zero_mod, ↓reduceDIte]
  · have hlt : location < 5534 := by omega
    have hmod : location % 5534 = location := Nat.mod_eq_of_lt hlt
    have hnonzero : location ≠ 0 := Nat.ne_of_gt hpositive.1
    simp only [hmod, hnonzero, ↓reduceDIte]
    apply And.intro <;> apply Fin.ext
    · change cert246Data.keyGroup
          (cert246Data.keyField cert246Data.lhsKeyEnc (location - 1)) % 138 = group
      rw [hpositive.2.2.1, Nat.mod_eq_of_lt group.isLt]
    · change cert246Data.keyTarget
          (cert246Data.keyField cert246Data.lhsKeyEnc (location - 1)) % 272 = target
      rw [hpositive.2.2.2, Nat.mod_eq_of_lt target.isLt]

/-- Every packed LHS transform key has in-range group and target components. -/
theorem certLhsKeys_bound : ∀ entry < 5533,
    let field := cert246Data.keyField cert246Data.lhsKeyEnc entry
    cert246Data.keyGroup field < 138 ∧ cert246Data.keyTarget field < 272 := by
  have hblocks : ∀ block : Fin 22, CertLhsKeysBlockCorrect block :=
    combine_batched_theorems% CertLhsKeysBlockCorrect 22
  intro entry hentry
  let block : Fin 22 := ⟨entry / 256, by omega⟩
  apply lhsKeysRangeCheck_sound (hblocks block) entry
  · dsimp only [block]
    exact Nat.div_mul_le_self entry 256
  · dsimp only [block]
    omega

/-- Every packed LHS location is zero or a valid one-based transform index. -/
theorem certLhsLocations_bound : ∀ group < 138, ∀ target < 272,
    cert246Data.treeAt 12 4095 16 65535 cert246Data.lhsLocationT
      (group * 272 + target) ≤ 5533 := by
  intro group hgroup target htarget
  rcases certLhsLocationIndex group hgroup target htarget with hzero | hpositive
  · rw [hzero]
    omega
  · exact hpositive.2.1

/-- Sparse LHS transform with direct evaluation outside its stored support. -/
noncomputable def certLhsTransform : Fin 138 → Fin 272 → ℤ :=
  preEpsWitnessInt.lhsSparseTransformGet certLhsPartition certLhsPartition_valid
    certLhsTransformValue certLhsTransformIndex

/-- One externally stored total of a fixed-degree LHS row. -/
noncomputable def certLhsStoredRow (group : Fin 138) : ℤ :=
  signedValue (cert246Data.treeAt 5 31 1088 (2 ^ 1088 - 1) cert246Data.lhsRowT group)

/-- One mathematical upper-triangular LHS degree row. -/
noncomputable def certLhsRow (group : Fin 138) : ℤ :=
  preEpsWitnessInt.lhsDegreeSymmetricRow certFactorTables certLhsPartition
    certLhsPartition_valid certLhsTransform group

end PrimeGaps.Gap246
