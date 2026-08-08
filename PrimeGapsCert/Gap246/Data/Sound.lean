/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Multiset.Sort
public import PrimeGapsCert.Gap246.Data.Defs
public import PrimeGapsCert.Gap246.Moments.CheckSound

/-! # Soundness of the dependency-isolated packed certificate data -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

open Finset

/-- Every generated signature row is structurally well formed. -/
theorem certRows : ∀ row < 272, RowFacts 272 12 cert246Data.sigEnc
    cert246Data.eraseEnc row (cert246Data.sigField cert246Data.sigEnc row)
      (cert246Data.sigCount (cert246Data.sigField cert246Data.sigEnc row)) :=
  dataCheck_sig_sound cert246Data.data_ok

/-- Every generated signature encoding fits its inspected nibbles. -/
theorem certEncoding : ∀ row < 272,
    cert246Data.sigField cert246Data.sigEnc row < 2 ^ (4 * (12 + 1)) :=
  fun row hrow ↦ (encCheck_sound cert246Data.enc_ok row hrow).1

/-- Every halved signature part is at most twelve. -/
theorem certParts : ∀ row < 272, ∀ position < 12,
    cert246Data.sigNib (cert246Data.sigField cert246Data.sigEnc row) position ≤ 12 :=
  fun row hrow ↦ (encCheck_sound cert246Data.enc_ok row hrow).2

/-- Every needed factorial-table field is its mathematical factorial. -/
theorem certFactorials : ∀ n ≤ 48,
    cert246Data.factAt cert246Data.factT n = n ! := fun n hn ↦ by
  simpa [cert246Data.factAt, Nat.shiftLeft_eq, Nat.mul_comm] using
    factCheck_sound cert246Data.fact_ok n (by omega)

/-- Every generated label has an in-range signature, the correct signature sum, and bounded
total degree. -/
theorem certLabels : ∀ label < 1295,
    cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label) < 272 ∧
    cert246Data.labelDegree (cert246Data.labelField cert246Data.labelEnc label) =
      2 * ∑ position ∈ Finset.range
        (cert246Data.sigCount (cert246Data.sigField cert246Data.sigEnc
          (cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label)))),
        cert246Data.sigNib
          (cert246Data.sigField cert246Data.sigEnc
            (cert246Data.labelSignature (cert246Data.labelField cert246Data.labelEnc label)))
          position ∧
    cert246Data.labelA (cert246Data.labelField cert246Data.labelEnc label) +
      cert246Data.labelDegree (cert246Data.labelField cert246Data.labelEnc label) ≤ 25 :=
  dataCheck_label_sound (by norm_num) cert246Data.data_ok

/-- Canonical ordered-list presentation of one packed signature. -/
noncomputable def certSig (row : ℕ) : List ℕ :=
  Multiset.sort (sigOf cert246Data.sigEnc row) (· ≤ ·)

/-- Forgetting the canonical order recovers the decoded signature multiset. -/
@[simp]
theorem certSig_coe (row : ℕ) :
    (certSig row : Multiset ℕ) = sigOf cert246Data.sigEnc row :=
  Multiset.sort_eq _ _

/-- Every canonical generated signature is zero-free. -/
theorem certSig_zeroFree (row : ℕ) (hrow : row < 272) : (0 : ℕ) ∉ certSig row := by
  intro hzero
  apply zero_notMem_decodeSig (fun position hposition ↦
    (certRows row hrow).nib_pos position hposition)
  change 0 ∈ sigOf cert246Data.sigEnc row
  rw [← certSig_coe row]
  exact Multiset.mem_coe.mpr hzero

/-- Every exponent in a canonical generated signature is below the generic degree bound. -/
theorem certSig_exponent_lt (row : ℕ) (hrow : row < 272) (x : ℕ)
    (hx : x ∈ certSig row) : x < 25 := by
  have hx' : x ∈ sigOf cert246Data.sigEnc row := by
    rw [← certSig_coe row]
    exact Multiset.mem_coe.mpr hx
  rw [sigOf, decodeSig_eq_map] at hx'
  simp only [Multiset.mem_coe, List.mem_map, List.mem_range] at hx'
  obtain ⟨position, hposition, rfl⟩ := hx'
  have hpart := certParts row hrow position (hposition.trans_le (certRows row hrow).count_le)
  omega

private theorem list_sum_range_eq_finset_sum (f : ℕ → ℕ) : ∀ count,
    ((List.range count).map f).sum = ∑ position ∈ Finset.range count, f position
  | 0 => by simp
  | count + 1 => by
      rw [List.range_succ, List.map_append, List.sum_append, list_sum_range_eq_finset_sum,
        Finset.sum_range_succ]
      simp

/-- The sum of the canonical list is the doubled sum of its packed nibbles. -/
theorem certSig_sum (row : ℕ) :
    (certSig row).sum =
      2 * ∑ position ∈ Finset.range
        (cert246Data.sigCount (cert246Data.sigField cert246Data.sigEnc row)),
        cert246Data.sigNib (cert246Data.sigField cert246Data.sigEnc row) position :=
  calc
    (certSig row).sum = (sigOf cert246Data.sigEnc row).sum := by
      simpa only [Multiset.sum_coe] using congrArg Multiset.sum (certSig_coe row)
    _ = _ := by
      rw [sigOf, decodeSig_eq_map, Multiset.sum_coe, List.sum_map_mul_left]
      simp only [Finset.sum_range]
      congr 1
      rw [Fin.sum_univ_eq_sum_range]
      exact list_sum_range_eq_finset_sum _ _

private theorem certSig_eq_erase_of_multiset {source target x : ℕ}
    (h : sigOf cert246Data.sigEnc target =
      (sigOf cert246Data.sigEnc source).erase x) :
    certSig target = (certSig source).erase x := by
  apply List.Perm.eq_of_pairwise'
    (Multiset.pairwise_sort (sigOf cert246Data.sigEnc target) (· ≤ ·))
  · change List.Pairwise (· ≤ ·)
      ((Multiset.sort (sigOf cert246Data.sigEnc source) (· ≤ ·)).erase x)
    exact (Multiset.pairwise_sort (sigOf cert246Data.sigEnc source) (· ≤ ·)).erase x
  apply Multiset.coe_eq_coe.mp
  rw [Multiset.sort_eq, ← Multiset.coe_erase, certSig_coe, h]

/-- Packed in-range signature label after erasing one exponent. -/
noncomputable def certErase (row : Fin 272) (x : ℕ) : Fin 272 :=
  if x = 0 then row
  else ⟨cert246Data.treeAt 10 1023 16 65535 cert246Data.eraseTargetT
    (row * 26 + x) % 272, Nat.mod_lt _ (by norm_num)⟩

/-- The chosen erasure label presents the canonical erased list. -/
theorem certErase_sig (row : Fin 272) (x : ℕ)
    (hx : x ∈ insert 0 (certSig row).toFinset) :
    certSig (certErase row x) = (certSig row).erase x := by
  rcases Finset.mem_insert.mp hx with rfl | hx
  · rw [certErase, if_pos rfl, List.erase_of_not_mem (certSig_zeroFree row row.isLt)]
  · have hx' : x ∈ sigOf cert246Data.sigEnc row := by
      rw [← certSig_coe row]
      exact Multiset.mem_coe.mpr (List.mem_toFinset.mp hx)
    have hstart : x ∈
        {position ∈ Finset.range (cert246Data.sigCount
          (cert246Data.sigField cert246Data.sigEnc row)) | position = 0 ∨
              cert246Data.sigNib (cert246Data.sigField cert246Data.sigEnc row) position ≠
                cert246Data.sigNib (cert246Data.sigField cert246Data.sigEnc row)
                  (position - 1)}.image
          (fun position ↦ 2 * cert246Data.sigNib
            (cert246Data.sigField cert246Data.sigEnc row) position) := by
      rw [distinct_starts_enumerate]
      exact Multiset.mem_toFinset.mpr hx'
    obtain ⟨position, hpositionRaw, hvalue⟩ := Finset.mem_image.mp hstart
    have hpositionRaw := (Finset.mem_filter.mp hpositionRaw).1
    have hposition := Finset.mem_range.mp hpositionRaw
    let target := cert246Data.treeAt 10 1023 16 65535 cert246Data.eraseTargetT
      (row * 26 + x)
    have htargetRaw := (eraseTargetCheck_sound cert246Data.erase_target_ok row row.isLt).2
      position hposition
    dsimp only at htargetRaw
    norm_num at htargetRaw
    rw [hvalue] at htargetRaw
    have htarget : target < 272 := htargetRaw.1
    have hfield : cert246Data.sigField cert246Data.sigEnc target =
        cert246Data.eraseAt (cert246Data.sigField cert246Data.sigEnc row) position :=
      htargetRaw.2
    have hxzero : x ≠ 0 := fun hzero ↦
      certSig_zeroFree row row.isLt (hzero ▸ List.mem_toFinset.mp hx)
    let rawTarget : Fin 272 := ⟨target, htarget⟩
    have herase : certErase row x = rawTarget := by
      rw [certErase, if_neg hxzero]
      exact Fin.ext (Nat.mod_eq_of_lt htarget)
    rw [herase]
    apply certSig_eq_erase_of_multiset
    rw [sigOf, hfield, sigOf, decodeSig_eraseAt hposition, hvalue]

end PrimeGaps.Gap246
