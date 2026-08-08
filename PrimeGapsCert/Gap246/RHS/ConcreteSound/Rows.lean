/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.RHS.ConcreteSound.Contraction
public import PrimeGapsCert.Gap246.Sparse.RhsRowSound


/-! # Concrete RHS row soundness -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Concrete upper-triangular RHS row indexed by offsets from its diagonal. -/
noncomputable def certRhsDirectRow (left : Fin 172) : ℤ :=
  ∑ offset ∈ Finset.range (172 - left),
    if left.val < left.val + offset then
      2 * certRhsPairNat left (left + offset)
    else certRhsPairNat left (left + offset)

/-- The same concrete RHS row written as a sum over all finite group indices. -/
noncomputable def certRhsFullRow (left : Fin 172) : ℤ :=
  ∑ right : Fin 172, if left < right then 2 * certRhsPair left right
    else if left = right then certRhsPair left right else 0

/-- The full concrete RHS row is the standard abstract transformed row. -/
theorem certRhsFullRow_eq (left : Fin 172) : certRhsFullRow left = certRhsRow left := by
  unfold certRhsFullRow certRhsRow
    PreEpsCertificateExplicitDagInt.rhsDegreeGroupSymmetricRowTransformed
  apply Finset.sum_congr rfl
  intro right _
  rw [certRhsPair_eq]

/-- The full finite RHS row is its natural-index range sum. -/
theorem certRhsFullRow_eq_range (left : Fin 172) :
    certRhsFullRow left =
      ∑ right ∈ Finset.range 172,
        if left.val < right then 2 * certRhsPairNat left right
        else if left.val = right then certRhsPairNat left right else 0 := by
  let f : ℕ → ℤ := fun right ↦
    if left.val < right then 2 * certRhsPairNat left right
    else if left.val = right then certRhsPairNat left right else 0
  change certRhsFullRow left = ∑ right ∈ Finset.range 172, f right
  calc
    certRhsFullRow left = ∑ right : Fin 172, f right.val := by
      unfold certRhsFullRow
      apply Finset.sum_congr rfl
      intro right _
      unfold f
      rw [certRhsPairNat_eq left right.val right.isLt]
      have hright : (⟨right.val, right.isLt⟩ : Fin 172) = right := Fin.ext rfl
      rw [hright]
      simp only [Fin.ext_iff]
      by_cases hlt : left < right
      · have hltNat : left.val < right.val := Fin.lt_def.mp hlt
        rw [if_pos hlt, if_pos hltNat]
      · have hltNat : ¬left.val < right.val :=
          fun h ↦ hlt (Fin.lt_def.mpr h)
        rw [if_neg hlt, if_neg hltNat]
    _ = ∑ right ∈ Finset.range 172, f right := Fin.sum_univ_eq_sum_range f 172

/-- The diagonal-offset RHS row equals the same row over all finite group indices. -/
theorem certRhsDirectRow_eq_full (left : Fin 172) :
    certRhsDirectRow left = certRhsFullRow left := by
  rw [certRhsFullRow_eq_range]
  unfold certRhsDirectRow
  let f : ℕ → ℤ := fun right ↦
    if left.val < right then 2 * certRhsPairNat left right
    else if left.val = right then certRhsPairNat left right else 0
  change (∑ offset ∈ Finset.range (172 - left),
      if left.val < left.val + offset then 2 * certRhsPairNat left (left + offset)
      else certRhsPairNat left (left + offset)) = ∑ right ∈ Finset.range 172, f right
  have hsplit : (∑ right ∈ Finset.range 172, f right) =
      (∑ right ∈ Finset.range left, f right) +
        ∑ offset ∈ Finset.range (172 - left), f (left + offset) := by
    have h := Finset.sum_range_add f left (172 - left)
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

/-- The offset-indexed concrete RHS row is the standard mathematical transformed row. -/
theorem certRhsDirectRow_eq (left : Fin 172) : certRhsDirectRow left = certRhsRow left :=
  (certRhsDirectRow_eq_full left).trans (certRhsFullRow_eq left)

/-- One raw RHS row specification is the concrete offset-indexed mathematical row. -/
theorem certRhsRowSpec_eq (hradial : CertRhsRadialChecks) (left : Fin 172)
    (hsupport : cert246Data.rhsSupportRowCheck 172 272 cert246Data.rhsFeatureEnc
      cert246Data.rhsGroupEnc 12 4095 cert246Data.rhsLocationT left = true) :
    rhsRowSpec 50 172 272 102 cert246Data.rhsFeatureEnc cert246Data.rhsGroupEnc
        12 4095 7 127 384 (2 ^ 384 - 1) 8 255 256 (2 ^ 256 - 1)
        6 63 832 (2 ^ 832 - 1) cert246Data.rhsLocationT
        cert246Data.rhsTransformT cert246Data.rhsWeightT cert246Data.rhsRadialT left =
      certRhsDirectRow left := by
  unfold rhsRowSpec certRhsDirectRow
  apply Finset.sum_congr rfl
  intro offset hoffset
  have hoffsetLt := Finset.mem_range.mp hoffset
  let rightNat := left.val + offset
  have hright : rightNat < 172 := by
    dsimp only [rightNat]
    omega
  let right : Fin 172 := ⟨rightNat, hright⟩
  let leftField := cert246Data.groupField cert246Data.rhsGroupEnc left.val
  let rightField := cert246Data.groupField cert246Data.rhsGroupEnc rightNat
  let q := 49 + cert246Data.groupLowDegree leftField +
    cert246Data.groupLowDegree rightField
  let e := cert246Data.groupHighDegree leftField +
    cert246Data.groupHighDegree rightField
  have hleftDegree := certRhsGroupDegree_bound left left.isLt
  have hrightDegree := certRhsGroupDegree_bound right right.isLt
  have hleftDegreeRaw : cert246Data.groupLowDegree leftField +
      cert246Data.groupHighDegree leftField ≤ 26 := by
    simpa only [leftField] using hleftDegree
  have hrightDegreeRaw : cert246Data.groupLowDegree rightField +
      cert246Data.groupHighDegree rightField ≤ 26 := by
    simpa only [rightField, right, Fin.val_mk] using hrightDegree
  have hq : 49 ≤ q := by
    dsimp only [q]
    omega
  have hqe : q + e ≤ 101 := by
    dsimp only [q, e]
    omega
  have hleftRight : left.val ≤ right.val := by
    dsimp only [right]
    omega
  have hqueries := rhsSupportRowCheck_sound hsupport right hleftRight right.isLt
  rw [certRhsPairNat_eq left rightNat hright]
  change Bool.rec
      (cert246Data.treeAt 6 63 832 (2 ^ 832 - 1) cert246Data.rhsRadialT
        (q * 102 + e) : ℤ)
      (2 * (cert246Data.treeAt 6 63 832 (2 ^ 832 - 1) cert246Data.rhsRadialT
        (q * 102 + e) : ℤ))
      (Nat.blt left.val rightNat) *
        rhsContractionSpec 272 cert246Data.rhsFeatureEnc cert246Data.rhsGroupEnc
          12 4095 7 127 384 (2 ^ 384 - 1) 8 255 256 (2 ^ 256 - 1)
          cert246Data.rhsLocationT cert246Data.rhsTransformT
          cert246Data.rhsWeightT left.val rightNat =
    if left.val < rightNat then 2 * certRhsPair left right
    else certRhsPair left right
  rw [certRhsRadial_correct hradial q e hq hqe]
  rw [certRhsContractionSpec_eq_of_support left right hqueries]
  unfold certRhsPair
  change Bool.rec (certFactorTables.radial q e : ℤ)
      (2 * (certFactorTables.radial q e : ℤ)) (Nat.blt left.val rightNat) *
        certRhsContraction left right =
      if left.val < rightNat then
        2 * ((certFactorTables.radial q e : ℤ) * certRhsContraction left right)
      else (certFactorTables.radial q e : ℤ) * certRhsContraction left right
  by_cases hlt : left.val < rightNat
  · have hblt : Nat.blt left.val rightNat = true := Nat.blt_eq.mpr hlt
    simp only [hblt, hlt, if_true]
    ring
  · have hblt : Nat.blt left.val rightNat = false :=
      Bool.eq_false_of_not_eq_true fun htrue ↦ hlt (Nat.blt_eq.mp htrue)
    simp only [hblt, hlt, if_false]

/-- One complete raw RHS row check implies equality with the mathematical row. -/
theorem certRhsRowCheck_correct (hradial : CertRhsRadialChecks) (left : Fin 172)
    (hcheck : cert246Data.rhsRowCheck 50 172 272 102 cert246Data.rhsFeatureEnc
      cert246Data.rhsGroupEnc 12 4095 7 127 384 (2 ^ 384 - 1)
      5 31 1088 (2 ^ 1088 - 1) 8 255 256 (2 ^ 256 - 1)
      6 63 832 (2 ^ 832 - 1) cert246Data.rhsLocationT
      cert246Data.rhsTransformT cert246Data.rhsRowT cert246Data.rhsWeightT
      cert246Data.rhsRadialT left (left + 1) = true) :
    certRhsStoredRow left = certRhsRow left := by
  have hstored := congrArg signedValue (rhsRowCheck_sound hcheck left (by omega) (by omega))
  have hsupport := rhsRowCheck_support_sound hcheck left (by omega) (by omega)
  unfold certRhsStoredRow
  rw [hstored]
  rw [rhsRowValue_sound]
  rw [certRhsRowSpec_eq hradial left hsupport]
  exact certRhsDirectRow_eq left

end PrimeGaps.Gap246
