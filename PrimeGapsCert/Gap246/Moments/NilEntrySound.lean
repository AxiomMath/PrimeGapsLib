/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.NilSupport
public import PrimeGapsCert.Gap246.Moments.ScanLemmas

/-! # Soundness of one identity-free table entry -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

open Finset

/-- The mathematical finite-sum form of the first-order identity-free kernel entry
through an arbitrary predecessor lookup. -/
noncomputable def nilRowValWith (eraseEnc factT : ℕ) (lookup : ℕ → ℕ → ℕ) (s t : ℕ) : ℕ :=
  (∑ j₁ ∈ Finset.range 4,
    if cert246Data.slotUsed (cert246Data.slotField eraseEnc s j₁) = true then
      ∑ j₂ ∈ Finset.range 5,
        if cert246Data.slotUsed (cert246Data.slotField eraseEnc t j₂) = true then
          cert246Data.factAt factT (Nat.shiftLeft
              (cert246Data.slotPart2 (cert246Data.slotField eraseEnc s j₁) +
                cert246Data.slotPart2 (cert246Data.slotField eraseEnc t j₂)) 1) *
          lookup (cert246Data.slotTarget (cert246Data.slotField eraseEnc s j₁))
            (cert246Data.slotTarget (cert246Data.slotField eraseEnc t j₂))
        else 0
    else 0) +
    ∑ j₂ ∈ Finset.range 4,
      if cert246Data.slotUsed (cert246Data.slotField eraseEnc t j₂) = true then
        cert246Data.factAt factT
            (Nat.shiftLeft
              (cert246Data.slotPart2 (cert246Data.slotField eraseEnc t j₂)) 1) *
          lookup s (cert246Data.slotTarget (cert246Data.slotField eraseEnc t j₂))
      else 0

private theorem bool_rec_add (used : Bool) (accumulator value : ℕ) :
    (Bool.rec accumulator (accumulator + value) used : ℕ) =
      accumulator + if used = true then value else 0 := by
  cases used <;> simp

private theorem bool_rec_add_five (used : Bool)
    (accumulator value₀ value₁ value₂ value₃ value₄ : ℕ) :
    (Bool.rec accumulator
        (accumulator + value₀ + value₁ + value₂ + value₃ + value₄) used : ℕ) =
      accumulator + if used = true then value₀ + value₁ + value₂ + value₃ + value₄ else 0 := by
  cases used <;> simp [Nat.add_assoc]

/-- The first-order kernel entry through any lookup is its finite-sum specification. -/
theorem nilEntryWith_eq_nilRowValWith (eraseEnc factT : ℕ) (lookup : ℕ → ℕ → ℕ)
    (s t : ℕ) :
    cert246Data.nilEntryWith eraseEnc factT lookup s t =
      nilRowValWith eraseEnc factT lookup s t := by
  unfold cert246Data.nilEntryWith nilRowValWith
  simp only [Nat.add_eq, Nat.mul_eq, bool_rec_add, bool_rec_add_five, Finset.sum_range_succ,
    Finset.sum_range_zero]
  simp only [Nat.zero_add, Nat.add_assoc]

/-! ## Decoding the five erase slots -/

/-- Adding back the omitted identity pair turns `nilRowValWith` into the full slot sum. -/
private theorem nilRowValWith_add_identity {eraseEnc factT : ℕ}
    {lookup : ℕ → ℕ → ℕ} {s t : ℕ} (hfact0 : cert246Data.factAt factT 0 = 1)
    (hidS : SlotId eraseEnc s) (hidT : SlotId eraseEnc t) :
    nilRowValWith eraseEnc factT lookup s t + lookup s t =
      ∑ j₁ ∈ Finset.range 5,
        if cert246Data.slotUsed (cert246Data.slotField eraseEnc s j₁) = true then
          ∑ j₂ ∈ Finset.range 5,
            if cert246Data.slotUsed (cert246Data.slotField eraseEnc t j₂) = true then
              cert246Data.factAt factT (Nat.shiftLeft
                  (cert246Data.slotPart2 (cert246Data.slotField eraseEnc s j₁) +
                    cert246Data.slotPart2 (cert246Data.slotField eraseEnc t j₂)) 1) *
                lookup (cert246Data.slotTarget (cert246Data.slotField eraseEnc s j₁))
                  (cert246Data.slotTarget (cert246Data.slotField eraseEnc t j₂))
            else 0
        else 0 := by
  have hinner :
      (∑ j₂ ∈ Finset.range 5,
        if cert246Data.slotUsed (cert246Data.slotField eraseEnc t j₂) = true then
          cert246Data.factAt factT (Nat.shiftLeft
              (0 + cert246Data.slotPart2 (cert246Data.slotField eraseEnc t j₂)) 1) *
            lookup s (cert246Data.slotTarget (cert246Data.slotField eraseEnc t j₂))
        else 0) =
      (∑ j₂ ∈ Finset.range 4,
        if cert246Data.slotUsed (cert246Data.slotField eraseEnc t j₂) = true then
          cert246Data.factAt factT
              (Nat.shiftLeft
                (cert246Data.slotPart2 (cert246Data.slotField eraseEnc t j₂)) 1) *
            lookup s (cert246Data.slotTarget (cert246Data.slotField eraseEnc t j₂))
        else 0) +
      lookup s t := by
    rw [Finset.sum_range_succ, hidT.used, hidT.part2, hidT.tgt]
    simp [hfact0]
  conv_rhs => rw [Finset.sum_range_succ]
  simp only [hidS.used, if_true, hidS.part2, hidS.tgt, hinner]
  unfold nilRowValWith
  ac_rfl

/-- A decoded first-order entry through any sound lookup is the identity-free
mathematical transition. -/
theorem nilRowValWith_eq_nilStep {S maxNib partBound sigEnc eraseEnc factT : ℕ}
    {lookup : ℕ → ℕ → ℕ} {state : MomentState} {s t : ℕ}
    (hS : S ≤ 512) (hs : s < S) (ht : t < S)
    (hrows : ∀ row < S, RowFacts S maxNib sigEnc eraseEnc row
      (cert246Data.sigField sigEnc row)
      (cert246Data.sigCount (cert246Data.sigField sigEnc row)))
    (hpart : ∀ row < S, ∀ position < maxNib,
      cert246Data.sigNib (cert246Data.sigField sigEnc row) position ≤ partBound)
    (hfact : ∀ n ≤ 4 * partBound, cert246Data.factAt factT n = n !)
    (hlookup : ∀ first < S, ∀ second < S,
      lookup first second = state (sigOf sigEnc first) (sigOf sigEnc second)) :
    nilRowValWith eraseEnc factT lookup s t =
      nilStep state (sigOf sigEnc s) (sigOf sigEnc t) := by
  have hzero : ∀ row < S, (0 : ℕ) ∉ sigOf sigEnc row := fun row hrow ↦
    zero_notMem_decodeSig fun position hposition ↦ (hrows row hrow).nib_pos position hposition
  have hfull :
      (∑ j₁ ∈ Finset.range 5,
        if cert246Data.slotUsed (cert246Data.slotField eraseEnc s j₁) = true then
          ∑ j₂ ∈ Finset.range 5,
            if cert246Data.slotUsed (cert246Data.slotField eraseEnc t j₂) = true then
              cert246Data.factAt factT (Nat.shiftLeft
                  (cert246Data.slotPart2 (cert246Data.slotField eraseEnc s j₁) +
                    cert246Data.slotPart2 (cert246Data.slotField eraseEnc t j₂)) 1) *
                lookup (cert246Data.slotTarget (cert246Data.slotField eraseEnc s j₁))
                  (cert246Data.slotTarget (cert246Data.slotField eraseEnc t j₂))
            else 0
        else 0) =
      ∑ x ∈ insert 0 (sigOf sigEnc s).toFinset,
        ∑ y ∈ insert 0 (sigOf sigEnc t).toFinset,
          (x + y) ! * state
            ((sigOf sigEnc s).erase x) ((sigOf sigEnc t).erase y) := by
    refine row_sum_eq (hrows s hs) rfl rfl (by omega) hs
      (fun position hposition ↦ hpart s hs position
        (Nat.lt_of_lt_of_le hposition (hrows s hs).count_le))
      (fun x ↦ ∑ y ∈ insert 0 (sigOf sigEnc t).toFinset,
        (x + y) ! * state
          ((sigOf sigEnc s).erase x) ((sigOf sigEnc t).erase y))
      (fun x2 target₁ ↦ ∑ j₂ ∈ Finset.range 5,
        if cert246Data.slotUsed (cert246Data.slotField eraseEnc t j₂) = true then
          cert246Data.factAt factT (Nat.shiftLeft
              (x2 + cert246Data.slotPart2 (cert246Data.slotField eraseEnc t j₂)) 1) *
            lookup target₁ (cert246Data.slotTarget (cert246Data.slotField eraseEnc t j₂))
        else 0) ?_
    intro x2 target₁ hx2 htarget₁ herase₁
    refine row_sum_eq (hrows t ht) rfl rfl (by omega) ht
      (fun position hposition ↦ hpart t ht position
        (Nat.lt_of_lt_of_le hposition (hrows t ht).count_le))
      (fun y ↦ (2 * x2 + y) ! * state
        ((sigOf sigEnc s).erase (2 * x2)) ((sigOf sigEnc t).erase y))
      (fun y2 target₂ ↦ cert246Data.factAt factT (Nat.shiftLeft (x2 + y2) 1) *
        lookup target₁ target₂) ?_
    intro y2 target₂ hy2 htarget₂ herase₂
    rw [(by simp [Nat.shiftLeft_eq]; ring :
      Nat.shiftLeft (x2 + y2) 1 = 2 * x2 + 2 * y2),
      hfact (2 * x2 + 2 * y2) (by omega),
      hlookup target₁ htarget₁ target₂ htarget₂, herase₁, herase₂]
  have hadd := nilRowValWith_add_identity (lookup := lookup)
    (by simpa using hfact 0 (Nat.zero_le _)) ((hrows s hs).slotId (by omega))
      ((hrows t ht).slotId (by omega))
  rw [hlookup s hs t ht, hfull, fullStep_eq_add_nilStep state (hzero s hs) (hzero t ht)] at hadd
  omega

end PrimeGaps.Gap246
