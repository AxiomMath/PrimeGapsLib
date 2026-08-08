/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.LHS.ConcreteSound.Scalar


/-! # Concrete soundness for packed sparse LHS rows -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- One concrete pair of LHS degree groups. -/
noncomputable def certLhsPair (left right : Fin 138) : ℤ :=
  let leftGroup := certLhsPartition.group left
  let rightGroup := certLhsPartition.group right
  certFactorTables.iScalar
      (leftGroup.distinguishedDegree + rightGroup.distinguishedDegree +
        leftGroup.signatureDegree + rightGroup.signatureDegree)
      (leftGroup.distinguishedDegree + rightGroup.distinguishedDegree) *
    certLhsContraction left right

/-- The concrete LHS group pair is the corresponding abstract group pair. -/
theorem certLhsPair_eq (left right : Fin 138) :
    certLhsPair left right =
      preEpsWitnessInt.lhsDegreePair certFactorTables certLhsPartition
        certLhsPartition_valid certLhsTransform left right := by
  unfold certLhsPair PreEpsCertificateExplicitDagInt.lhsDegreePair
  rw [certLhsContraction_eq]
  simp only [Nat.add_assoc]

/-- A concrete LHS pair addressed by a natural group index, or zero out of range. -/
noncomputable def certLhsPairNat (left : Fin 138) (right : ℕ) : ℤ :=
  if hright : right < 138 then certLhsPair left ⟨right, hright⟩ else 0

/-- An in-range natural group index reads the corresponding concrete pair. -/
theorem certLhsPairNat_eq (left : Fin 138) (right : ℕ) (hright : right < 138) :
    certLhsPairNat left right = certLhsPair left ⟨right, hright⟩ := by
  simp only [certLhsPairNat, dif_pos hright]

/-- Concrete upper-triangular LHS row indexed by offsets from its diagonal. -/
noncomputable def certLhsDirectRow (left : Fin 138) : ℤ :=
  ∑ offset ∈ Finset.range (138 - left),
    if left.val < left.val + offset then
      2 * certLhsPairNat left (left + offset)
    else certLhsPairNat left (left + offset)

/-- The same concrete row written as a sum over all finite group indices. -/
noncomputable def certLhsFullRow (left : Fin 138) : ℤ :=
  ∑ right : Fin 138, if left < right then 2 * certLhsPair left right
    else if left = right then certLhsPair left right else 0

/-- The full concrete row is the standard abstract mathematical row. -/
theorem certLhsFullRow_eq (left : Fin 138) : certLhsFullRow left = certLhsRow left := by
  unfold certLhsFullRow certLhsRow PreEpsCertificateExplicitDagInt.lhsDegreeSymmetricRow
  apply Finset.sum_congr rfl
  intro right _
  rw [certLhsPair_eq]

/-- The full finite row is its natural-index range sum. -/
theorem certLhsFullRow_eq_range (left : Fin 138) :
    certLhsFullRow left =
      ∑ right ∈ Finset.range 138,
        if left.val < right then 2 * certLhsPairNat left right
        else if left.val = right then certLhsPairNat left right else 0 := by
  let f : ℕ → ℤ := fun right ↦
    if left.val < right then 2 * certLhsPairNat left right
    else if left.val = right then certLhsPairNat left right else 0
  change certLhsFullRow left = ∑ right ∈ Finset.range 138, f right
  calc
    certLhsFullRow left = ∑ right : Fin 138, f right.val := by
      unfold certLhsFullRow
      apply Finset.sum_congr rfl
      intro right _
      unfold f
      rw [certLhsPairNat_eq left right.val right.isLt]
      have hright : (⟨right.val, right.isLt⟩ : Fin 138) = right := Fin.ext rfl
      rw [hright]
      simp only [Fin.ext_iff]
      by_cases hlt : left < right
      · have hltNat : left.val < right.val := Fin.lt_def.mp hlt
        rw [if_pos hlt, if_pos hltNat]
      · have hltNat : ¬left.val < right.val :=
          fun h ↦ hlt (Fin.lt_def.mpr h)
        rw [if_neg hlt, if_neg hltNat]
    _ = ∑ right ∈ Finset.range 138, f right := Fin.sum_univ_eq_sum_range f 138

/-- The diagonal-offset row equals the same row over all finite group indices. -/
theorem certLhsDirectRow_eq_full (left : Fin 138) :
    certLhsDirectRow left = certLhsFullRow left := by
  rw [certLhsFullRow_eq_range]
  unfold certLhsDirectRow
  let f : ℕ → ℤ := fun right ↦
    if left.val < right then 2 * certLhsPairNat left right
    else if left.val = right then certLhsPairNat left right else 0
  change (∑ offset ∈ Finset.range (138 - left),
      if left.val < left.val + offset then 2 * certLhsPairNat left (left + offset)
      else certLhsPairNat left (left + offset)) = ∑ right ∈ Finset.range 138, f right
  have hsplit : (∑ right ∈ Finset.range 138, f right) =
      (∑ right ∈ Finset.range left, f right) +
        ∑ offset ∈ Finset.range (138 - left), f (left + offset) := by
    have h := Finset.sum_range_add f left (138 - left)
    rwa [Nat.add_sub_of_le (Nat.le_of_lt left.isLt)] at h
  rw [hsplit]
  have hbelow : (∑ right ∈ Finset.range left, f right) = 0 := by
    apply Finset.sum_eq_zero
    intro right hright
    have hlt := Finset.mem_range.mp hright
    simp only [f, not_lt.mpr (Nat.le_of_lt hlt), ne_of_gt hlt, if_false]
  rw [hbelow, zero_add]
  apply Finset.sum_congr rfl
  intro offset _
  unfold f
  by_cases hlt : left.val < left.val + offset
  · rw [if_pos hlt, if_pos hlt]
  · have heq : left.val = left.val + offset := by omega
    rw [if_neg hlt, if_neg hlt, if_pos heq]

/-- The offset-indexed concrete row is the standard mathematical symmetric row. -/
theorem certLhsDirectRow_eq (left : Fin 138) : certLhsDirectRow left = certLhsRow left :=
  (certLhsDirectRow_eq_full left).trans (certLhsFullRow_eq left)

/-- One raw LHS row specification is the concrete offset-indexed mathematical row. -/
theorem certLhsRowSpec_eq (left : Fin 138)
    (hsupport : cert246Data.lhsSupportRowCheck 138 272 cert246Data.lhsMemberEnc
      cert246Data.labelEnc cert246Data.lhsGroupEnc 12 4095
      cert246Data.lhsLocationT left = true) :
    lhsRowSpec 138 272 51 cert246Data.lhsMemberEnc cert246Data.labelEnc
        cert246Data.lhsGroupEnc 12 4095 7 127 320 (2 ^ 320 - 1) 9 511 128
        (2 ^ 128 - 1) 6 63 1024 cert246Data.lhsScalarMask
        cert246Data.lhsLocationT cert246Data.lhsTransformT cert246Data.coeffMag
        cert246Data.lhsScalarT left = certLhsDirectRow left := by
  unfold lhsRowSpec certLhsDirectRow
  apply Finset.sum_congr rfl
  intro offset hoffset
  have hoffsetLt := Finset.mem_range.mp hoffset
  let rightNat := left.val + offset
  have hright : rightNat < 138 := by
    dsimp only [rightNat]
    omega
  let right : Fin 138 := ⟨rightNat, hright⟩
  let leftField := cert246Data.groupField cert246Data.lhsGroupEnc left.val
  let rightField := cert246Data.groupField cert246Data.lhsGroupEnc rightNat
  let d := cert246Data.groupLowDegree leftField + cert246Data.groupLowDegree rightField +
    cert246Data.groupHighDegree leftField + cert246Data.groupHighDegree rightField
  let aSum := cert246Data.groupLowDegree leftField + cert246Data.groupLowDegree rightField
  have hleftDegree := certLhsGroupDegree_bound left left.isLt
  have hrightDegree := certLhsGroupDegree_bound right right.isLt
  have hleftDegreeRaw : cert246Data.groupLowDegree leftField +
      cert246Data.groupHighDegree leftField ≤ 25 := by
    simpa only [leftField] using hleftDegree
  have hrightDegreeRaw : cert246Data.groupLowDegree rightField +
      cert246Data.groupHighDegree rightField ≤ 25 := by
    simpa only [rightField, right, Fin.val_mk] using hrightDegree
  have hd : d ≤ 50 := by
    dsimp only [d]
    omega
  have haSum : aSum ≤ d := by
    dsimp only [aSum, d]
    omega
  have hleftRight : left.val ≤ right.val := by
    dsimp only [right]
    omega
  have hqueries := lhsSupportRowCheck_sound hsupport right hleftRight right.isLt
  rw [certLhsPairNat_eq left rightNat hright]
  change Bool.rec
      (cert246Data.treeAt 6 63 1024 cert246Data.lhsScalarMask
        cert246Data.lhsScalarT (d * 51 + aSum) : ℤ)
      (2 * (cert246Data.treeAt 6 63 1024 cert246Data.lhsScalarMask
        cert246Data.lhsScalarT (d * 51 + aSum) : ℤ))
      (Nat.blt left.val rightNat) *
        lhsContractionSpec 272 cert246Data.lhsMemberEnc cert246Data.labelEnc
          cert246Data.lhsGroupEnc 12 4095 7 127 320 (2 ^ 320 - 1) 9 511 128
          (2 ^ 128 - 1) cert246Data.lhsLocationT cert246Data.lhsTransformT
          cert246Data.coeffMag left.val rightNat =
    if left.val < rightNat then 2 * certLhsPair left right
    else certLhsPair left right
  rw [certLhsScalar_correct d aSum hd haSum]
  rw [certLhsContractionSpec_eq_of_support left right hqueries]
  unfold certLhsPair
  change Bool.rec (certFactorTables.iScalar d aSum : ℤ)
      (2 * (certFactorTables.iScalar d aSum : ℤ)) (Nat.blt left.val rightNat) *
        certLhsContraction left right =
      if left.val < rightNat then
        2 * ((certFactorTables.iScalar d aSum : ℤ) * certLhsContraction left right)
      else (certFactorTables.iScalar d aSum : ℤ) * certLhsContraction left right
  by_cases hlt : left.val < rightNat
  · have hblt : Nat.blt left.val rightNat = true := Nat.blt_eq.mpr hlt
    simp only [hblt, hlt, if_true]
    ring
  · have hblt : Nat.blt left.val rightNat = false :=
      Bool.eq_false_of_not_eq_true fun htrue ↦ hlt (Nat.blt_eq.mp htrue)
    simp only [hblt, hlt, if_false]

/-- One complete raw LHS row check implies equality with the mathematical row. -/
theorem certLhsRowCheck_correct (left : Fin 138)
    (hcheck : cert246Data.lhsRowCheck 138 272 51 cert246Data.lhsMemberEnc
      cert246Data.labelEnc cert246Data.lhsGroupEnc 12 4095 7 127 320
      (2 ^ 320 - 1) 5 31 1088 (2 ^ 1088 - 1) 9 511 128 (2 ^ 128 - 1)
      6 63 1024 cert246Data.lhsScalarMask cert246Data.lhsLocationT
      cert246Data.lhsTransformT cert246Data.lhsRowT cert246Data.coeffMag
      cert246Data.lhsScalarT left (left + 1) = true) :
    certLhsStoredRow left = certLhsRow left := by
  have hstored := lhsRowCheck_sound hcheck left (by omega) (by omega)
  have hsupport := lhsRowCheck_support_sound hcheck left (by omega) (by omega)
  unfold certLhsStoredRow
  rw [hstored]
  rw [lhsRowValue_sound]
  rw [certLhsRowSpec_eq left hsupport]
  exact certLhsDirectRow_eq left

end PrimeGaps.Gap246
