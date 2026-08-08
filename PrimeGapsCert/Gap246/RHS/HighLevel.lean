/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Certificate.Defs
public import PrimeGapsCert.Gap246.RHS.Defs
public import PrimeGapsCert.Gap246.Sparse.RhsIndexSound
import PrimeGapsCert.Gap246.RHS.Checks.Index
import PrimeGapsCert.Meta.Batched

/-! # Mathematical interface to the packed sparse RHS data -/

set_option maxRecDepth 100000

@[expose] public section

namespace PrimeGaps.Gap246

/-- One packed RHS marginal feature. -/
noncomputable def certRhsFeature (index : Fin 1504) : RhsMarginalFeature 272 :=
  let field := cert246Data.rhsFeatureField cert246Data.rhsFeatureEnc index
  {
    signature := ⟨cert246Data.rhsFeatureSignature field % 272, by omega⟩
    residualDegree := cert246Data.rhsFeatureResidual field
    radialDegree := cert246Data.rhsFeatureRadial field
    weight := signedValue (cert246Data.treeAt 8 255 256 (2 ^ 256 - 1)
      cert246Data.rhsWeightT index)
  }

/-- Consecutive RHS groups with fixed residual and radial degrees. -/
noncomputable def certRhsPartition : RhsDegreePartition 1504 172 :=
  {
    group := fun group ↦
      let field := cert246Data.groupField cert246Data.rhsGroupEnc group
      {
        start := cert246Data.groupStart field
        size := cert246Data.groupSize field
        residualDegree := cert246Data.groupLowDegree field
        radialDegree := cert246Data.groupHighDegree field
      }
    locateGroup := fun feature ↦
      let field := cert246Data.inverseField cert246Data.rhsInverseEnc feature
      ⟨cert246Data.inverseGroup field % 172, by omega⟩
    locateOffset := fun feature ↦
      cert246Data.inverseOffset
        (cert246Data.inverseField cert246Data.rhsInverseEnc feature)
  }

/-- The generated RHS groups enumerate all features with their recorded degree keys. -/
theorem certRhsPartition_valid : certRhsPartition.Valid certRhsFeature := by
  refine { bound := ?_, locateOffset_lt := ?_, right_inv := ?_, left_inv := ?_, key := ?_ } <;>
    decide +kernel

/-- Every packed RHS group lies inside the flattened feature array. -/
theorem certRhsPartition_bound : ∀ group,
    (certRhsPartition.group group).start + (certRhsPartition.group group).size ≤ 1504 :=
  certRhsPartition_valid.bound

/-- Each RHS group's residual-plus-radial degree is at most one above the degree bound. -/
theorem certRhsGroupDegree_bound : ∀ group < 172,
    let field := cert246Data.groupField cert246Data.rhsGroupEnc group
    cert246Data.groupLowDegree field + cert246Data.groupHighDegree field ≤ 26 := by
  decide +kernel

/-- Packed location of the marginal feature representing one label-and-erasure transition. -/
noncomputable abbrev certRhsLocations : Fin 1295 → Fin 26 → Fin 1504 := fun label exponent ↦
  ⟨cert246Data.treeAt 10 1023 16 65535 cert246Data.rhsSourceLocationT
    (label * 26 + exponent) % 1504, by omega⟩

/-- One externally stored sparse RHS-transform value. -/
noncomputable def certRhsTransformValue (entry : Fin 6057) : ℤ :=
  signedValue (cert246Data.treeAt 7 127 384 (2 ^ 384 - 1)
    cert246Data.rhsTransformT entry)

/-- Sparse locations and keys for the RHS transform. -/
noncomputable def certRhsTransformIndex : LhsSparseTransformIndex 172 272 6057 :=
  {
    location := fun group target ↦
      ⟨cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
        (group * 272 + target) % 6058, by omega⟩
    entryGroup := fun entry ↦
      ⟨cert246Data.keyGroup
        (cert246Data.keyField cert246Data.rhsKeyEnc entry) % 172, by omega⟩
    entryTarget := fun entry ↦
      ⟨cert246Data.keyTarget
        (cert246Data.keyField cert246Data.rhsKeyEnc entry) % 272, by omega⟩
  }

/-- Every nonzero sparse RHS location is bounded and decodes to its queried key. -/
theorem certRhsLocationIndex : ∀ group < 172, ∀ target < 272,
    let location := cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
      (group * 272 + target)
    location = 0 ∨
      (0 < location ∧ location ≤ 6057 ∧
        cert246Data.keyGroup
            (cert246Data.keyField cert246Data.rhsKeyEnc (location - 1)) = group ∧
          cert246Data.keyTarget
            (cert246Data.keyField cert246Data.rhsKeyEnc (location - 1)) = target) := by
  have hblocks : ∀ block : Fin 22, CertRhsLocationBlockCorrect block :=
    combine_batched_theorems% CertRhsLocationBlockCorrect 22
  intro group hgroup target htarget
  let block : Fin 22 := ⟨group / 8, by omega⟩
  apply rhsLocationIndexRangeCheck_sound (hblocks block) group
  · dsimp only [block]
    exact Nat.div_mul_le_self group 8
  · dsimp only [block]
    omega
  · exact htarget

/-- Every positive sparse RHS location points back to its group and target. -/
theorem certRhsTransformIndex_valid : certRhsTransformIndex.Valid := by
  refine { right_inv := ?_ }
  intro group target
  let location := cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
    (group * 272 + target)
  have hindex := certRhsLocationIndex group group.isLt target target.isLt
  change location = 0 ∨
    (0 < location ∧ location ≤ 6057 ∧
      cert246Data.keyGroup
          (cert246Data.keyField cert246Data.rhsKeyEnc (location - 1)) = group ∧
        cert246Data.keyTarget
          (cert246Data.keyField cert246Data.rhsKeyEnc (location - 1)) = target) at hindex
  change if h : location % 6058 = 0 then True else
    (⟨cert246Data.keyGroup
        (cert246Data.keyField cert246Data.rhsKeyEnc (location % 6058 - 1)) % 172,
        by omega⟩ : Fin 172) = group ∧
      (⟨cert246Data.keyTarget
        (cert246Data.keyField cert246Data.rhsKeyEnc (location % 6058 - 1)) % 272,
        by omega⟩ : Fin 272) = target
  rcases hindex with hzero | hpositive
  · simp only [hzero, Nat.zero_mod, ↓reduceDIte]
  · have hlt : location < 6058 := by omega
    have hmod : location % 6058 = location := Nat.mod_eq_of_lt hlt
    have hnonzero : location ≠ 0 := Nat.ne_of_gt hpositive.1
    simp only [hmod, hnonzero, ↓reduceDIte]
    apply And.intro <;> apply Fin.ext
    · change cert246Data.keyGroup
          (cert246Data.keyField cert246Data.rhsKeyEnc (location - 1)) % 172 = group
      rw [hpositive.2.2.1, Nat.mod_eq_of_lt group.isLt]
    · change cert246Data.keyTarget
          (cert246Data.keyField cert246Data.rhsKeyEnc (location - 1)) % 272 = target
      rw [hpositive.2.2.2, Nat.mod_eq_of_lt target.isLt]

/-- Every packed RHS transform key has in-range group and target components. -/
theorem certRhsKeys_bound : ∀ entry < 6057,
    let field := cert246Data.keyField cert246Data.rhsKeyEnc entry
    cert246Data.keyGroup field < 172 ∧ cert246Data.keyTarget field < 272 := by
  have hblocks : ∀ block : Fin 24, CertRhsKeysBlockCorrect block :=
    combine_batched_theorems% CertRhsKeysBlockCorrect 24
  intro entry hentry
  let block : Fin 24 := ⟨entry / 256, by omega⟩
  apply rhsKeysRangeCheck_sound (hblocks block) entry
  · dsimp only [block]
    exact Nat.div_mul_le_self entry 256
  · dsimp only [block]
    omega

/-- Every packed RHS location is zero or a valid one-based transform index. -/
theorem certRhsLocations_bound : ∀ group < 172, ∀ target < 272,
    cert246Data.treeAt 12 4095 16 65535 cert246Data.rhsLocationT
      (group * 272 + target) ≤ 6057 := by
  intro group hgroup target htarget
  rcases certRhsLocationIndex group hgroup target htarget with hzero | hpositive
  · rw [hzero]
    omega
  · exact hpositive.2.1

/-- Sparse RHS transform with direct evaluation outside its stored support. -/
noncomputable def certRhsTransform : Fin 172 → Fin 272 → ℤ :=
  preEpsWitnessInt.rhsSparseTransformGet certRhsFeature certRhsPartition
    certRhsPartition_valid certRhsTransformValue certRhsTransformIndex

/-- One externally stored total of a fixed-degree RHS row. -/
noncomputable def certRhsStoredRow (group : Fin 172) : ℤ :=
  signedValue (cert246Data.treeAt 5 31 1088 (2 ^ 1088 - 1) cert246Data.rhsRowT group)

/-- One mathematical upper-triangular RHS degree row. -/
noncomputable def certRhsRow (group : Fin 172) : ℤ :=
  preEpsWitnessInt.rhsDegreeGroupSymmetricRowTransformed certFactorTables certRhsFeature
    certRhsPartition certRhsPartition_valid certRhsTransform group

end PrimeGaps.Gap246
