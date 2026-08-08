/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.Direct.DecodeSound

/-! # Decoding lemmas for the checked signature rows

The scan of a checked signature row is shared by the two consumers of the packed moment
data: the hoisted ladder (`PrimeGapsCert.Gap246.Moments.Direct.LadderSound`) and the
identity-free table entry (`PrimeGapsCert.Gap246.Moments.NilEntrySound`). `row_sum_eq`
is the interface both use: the gated sum over the five erase slots of a row is the sum
over the distinct parts of its decoded signature together with `0`.
-/

@[expose] public section

namespace PrimeGaps.Gap246

section scanLemmas

open cert246Kernel Nat
open cert246Data (sigField sigCount sigNib eraseAt slotField slotUsed slotPart2 slotTarget)

/-! ### Distinct-value starts and slot indices -/

/-- A distinct-value start increments the running count of distinct-value starts. -/
theorem distinctCount_succ_of_start {enc p : ℕ}
    (h : p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1)) :
    distinctCount enc (p + 1) = distinctCount enc p + 1 := by simp [distinctCount, h]

/-- The running count of distinct-value starts is monotone in the cursor. -/
theorem distinctCount_mono (enc : ℕ) {a b : ℕ} (hab : a ≤ b) :
    distinctCount enc a ≤ distinctCount enc b := by
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => exact ih.trans (by simp only [distinctCount]; split <;> omega)

/-- Every slot index below the row's distinct-part count comes from a distinct-value start. -/
theorem exists_start_of_lt (enc : ℕ) : ∀ m j, j < distinctCount enc m →
    ∃ p < m, (p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1)) ∧ distinctCount enc p = j := by
  intro m
  induction m with
  | zero => exact fun j hj => by simp [distinctCount] at hj
  | succ m ih =>
    intro j hj
    rcases Nat.lt_or_ge j (distinctCount enc m) with h1 | h1
    · obtain ⟨p, hp, h2, h3⟩ := ih j h1
      exact ⟨p, by omega, h2, h3⟩
    · have hs : m = 0 ∨ sigNib enc m ≠ sigNib enc (m - 1) := by grind [distinctCount]
      rw [distinctCount_succ_of_start hs] at hj
      exact ⟨m, by omega, hs, by omega⟩

/-- A distinct-value start has a slot index below the row's distinct-part count. -/
theorem distinctCount_lt {enc m p : ℕ} (hp : p < m)
    (hs : p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1)) :
    distinctCount enc p < distinctCount enc m := by
  have h1 := distinctCount_mono enc hp
  rw [distinctCount_succ_of_start hs] at h1
  omega

/-- Nibbles that are monotone at adjacent positions are monotone across the whole part
range. -/
theorem sigNib_le_of_le {enc m : ℕ}
    (hmono : ∀ p < m, 0 < p → sigNib enc (p - 1) ≤ sigNib enc p) {a b : ℕ} (hab : a ≤ b) :
    b < m → sigNib enc a ≤ sigNib enc b := by
  induction b, hab using Nat.le_induction with
  | base => exact fun _ => le_rfl
  | succ b _ ih =>
    exact fun hbm => (ih (by omega)).trans (by simpa using hmono (b + 1) hbm (by omega))

/-- Distinct-value starts carry distinct nibble values. -/
theorem start_inj {enc m : ℕ}
    (hmono : ∀ p < m, 0 < p → sigNib enc (p - 1) ≤ sigNib enc p) {p q : ℕ}
    (hp : p < m) (hq : q < m)
    (hps : p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1))
    (hqs : q = 0 ∨ sigNib enc q ≠ sigNib enc (q - 1))
    (hval : sigNib enc p = sigNib enc q) : p = q := by
  have key : ∀ a b : ℕ, a < b → b < m → (b = 0 ∨ sigNib enc b ≠ sigNib enc (b - 1)) →
      sigNib enc a < sigNib enc b := fun a b hab hbm hbs => by
    have h1 : sigNib enc a ≤ sigNib enc (b - 1) := sigNib_le_of_le hmono (by omega) (by omega)
    have h2 := hmono b hbm (by omega)
    have h3 := hbs.resolve_left (by omega : ¬ b = 0)
    omega
  rcases Nat.lt_trichotomy p q with h | h | h
  · exact absurd hval (Nat.ne_of_lt (key p q h hq hqs))
  · exact h
  · exact absurd hval.symm (Nat.ne_of_lt (key q p h hp hps))

/-! ### The five erase slots of one row -/

private theorem slotUsed_zero : slotUsed 0 = false := by decide

/-- Slot `4` of a checked signature row is the identity slot. -/
theorem RowFacts.slotId {S maxNib sigEnc eraseEnc g enc m : ℕ} (hg : g < 512)
    (hrow : RowFacts S maxNib sigEnc eraseEnc g enc m) : SlotId eraseEnc g := by
  have hv : slotField eraseEnc g 4 = 32 * g + 1 := by
    simp [hrow.slot_id, Nat.shiftLeft_eq, Nat.mul_comm]
  have h1 : ∀ x : ℕ, x &&& 1 = x % 2 := Nat.and_one_is_mod
  have h15 : ∀ x : ℕ, x &&& 15 = x % 16 := fun x => Nat.and_two_pow_sub_one_eq_mod x 4
  have h511 : ∀ x : ℕ, x &&& 511 = x % 512 := fun x => by
    simpa using Nat.and_two_pow_sub_one_eq_mod x 9
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [slotUsed, slotPart2, slotTarget, hv, h1, h15, h511, Nat.shiftRight_eq_div_pow] <;>
    omega

/-- The used slots of a checked row are the identity slot and the distinct-part slots. -/
theorem used_slots_eq {S maxNib sigEnc eraseEnc g enc m : ℕ} (hg : g < 512)
    (hrow : RowFacts S maxNib sigEnc eraseEnc g enc m) :
    {j ∈ Finset.range 5 | slotUsed (slotField eraseEnc g j) = true} =
      insert 4 (Finset.range (distinctCount enc m)) := by
  have hD := hrow.distinct_le
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_insert]
  constructor
  · rintro ⟨hj5, hused⟩
    by_contra hcon
    simp only [not_or, Nat.not_lt] at hcon
    simp [hrow.slot_zero j hcon.2 (by omega), slotUsed_zero] at hused
  · rintro (rfl | hj)
    · exact ⟨by omega, (hrow.slotId hg).used⟩
    · obtain ⟨p, hp, hs, hdc⟩ := exists_start_of_lt enc m j hj
      rw [← hdc]
      exact ⟨by omega, (hrow.slot_match p hp hs).used⟩

/-- The gated slot sum of a checked row, as a sum over the distinct parts of its signature
together with `0`. -/
theorem row_sum_eq {S maxNib partBound sigEnc eraseEnc g enc m : ℕ}
    (hrow : RowFacts S maxNib sigEnc eraseEnc g enc m) (hm : m = sigCount enc)
    (hgenc : sigField sigEnc g = enc) (hg512 : g < 512) (hg : g < S)
    (hnib : ∀ p < m, sigNib enc p ≤ partBound)
    (F : ℕ → ℕ) (H : ℕ → ℕ → ℕ)
    (hH : ∀ x2 τ, x2 ≤ partBound → τ < S →
      sigOf sigEnc τ = (sigOf sigEnc g).erase (2 * x2) → H x2 τ = F (2 * x2)) :
    (∑ j ∈ Finset.range 5, if slotUsed (slotField eraseEnc g j) = true then
        H (slotPart2 (slotField eraseEnc g j)) (slotTarget (slotField eraseEnc g j)) else 0) =
      ∑ x ∈ insert 0 (sigOf sigEnc g).toFinset, F x := by
  have hD := hrow.distinct_le
  have hsig : sigOf sigEnc g = decodeSig enc := by rw [sigOf, hgenc]
  have hzero : (0 : ℕ) ∉ decodeSig enc :=
    zero_notMem_decodeSig fun p hp => hrow.nib_pos p (by omega)
  have hslot : ∀ j < distinctCount enc m, ∃ p < m,
      (p = 0 ∨ sigNib enc p ≠ sigNib enc (p - 1)) ∧ distinctCount enc p = j ∧
        SlotMatch S sigEnc eraseEnc g enc j p := by
    intro j hj
    obtain ⟨p, hp, hs, hdc⟩ := exists_start_of_lt enc m j hj
    rw [← hdc]
    exact ⟨p, hp, hs, rfl, hrow.slot_match p hp hs⟩
  rw [← Finset.sum_filter, used_slots_eq hg512 hrow, hsig,
    Finset.sum_insert (by simp only [Finset.mem_range]; omega),
    Finset.sum_insert (by simpa using hzero)]
  have hid := hrow.slotId hg512
  congr 1
  · rw [hid.part2, hid.tgt, hH 0 g (by omega) hg
      (by rw [Nat.mul_zero, hsig, Multiset.erase_of_notMem hzero]), Nat.mul_zero]
  · refine Finset.sum_bij (fun j _ => 2 * slotPart2 (slotField eraseEnc g j)) ?_ ?_ ?_ ?_
    · intro j hj
      obtain ⟨p, hp, hs, hdc, hsm⟩ := hslot j (Finset.mem_range.mp hj)
      rw [hsm.part2, ← distinct_starts_enumerate enc]
      exact Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
        ⟨Finset.mem_range.mpr (by omega), hs⟩, rfl⟩
    · intro j₁ hj₁ j₂ hj₂ heq
      obtain ⟨p₁, hp₁, hs₁, hdc₁, hsm₁⟩ := hslot j₁ (Finset.mem_range.mp hj₁)
      obtain ⟨p₂, hp₂, hs₂, hdc₂, hsm₂⟩ := hslot j₂ (Finset.mem_range.mp hj₂)
      rw [hsm₁.part2, hsm₂.part2] at heq
      rw [← hdc₁, ← hdc₂, start_inj hrow.nib_mono hp₁ hp₂ hs₁ hs₂ (by omega)]
    · intro x hx
      rw [← distinct_starts_enumerate enc] at hx
      obtain ⟨p, hpf, hpx⟩ := Finset.mem_image.mp hx
      obtain ⟨hpr, hs⟩ := Finset.mem_filter.mp hpf
      have hp : p < m := by rw [hm]; exact Finset.mem_range.mp hpr
      refine ⟨distinctCount enc p, Finset.mem_range.mpr (distinctCount_lt hp hs), ?_⟩
      rw [(hrow.slot_match p hp hs).part2, hpx]
    · intro j hj
      obtain ⟨p, hp, hs, hdc, hsm⟩ := hslot j (Finset.mem_range.mp hj)
      refine hH _ _ (hsm.part2.trans_le (hnib p hp)) hsm.tgt_lt ?_
      rw [sigOf, hsm.tgt_field, hsig, hsm.part2, decodeSig_eraseAt (by omega)]

end scanLemmas

end PrimeGaps.Gap246
