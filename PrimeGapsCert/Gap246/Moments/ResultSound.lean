/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.LadderSound

/-! # Soundness of the binomial reconstruction -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

private theorem gatedScan_sound (used : ℕ → Bool) (value : ℕ → ℕ) :
    ∀ count cursor accumulator,
      Nat.rec
        (fun _ accumulator' ↦ accumulator')
        (fun _ inductionHypothesis cursor' accumulator' ↦
          inductionHypothesis cursor'.succ
            (Bool.rec accumulator' (accumulator' + value cursor') (used cursor')))
        count cursor accumulator =
      accumulator + ∑ i ∈ Finset.range count,
        if used (cursor + i) = true then value (cursor + i) else 0
  | 0, _, _ => by simp
  | count + 1, cursor, accumulator => by
      dsimp only
      rw [gatedScan_sound used value count cursor.succ
        (Bool.rec accumulator (accumulator + value cursor) (used cursor)),
        sum_range_head
          (fun i ↦ if used i = true then value i else 0) cursor count]
      rcases used cursor <;> simp
      omega

/-- Above the combined signature cardinality, every term in a binomial moment vanishes. -/
theorem binomialMoment_eq_sum_card (dimension : ℕ) (left right : Multiset ℕ)
    (hcount : left.card + right.card ≤ dimension) :
    binomialMoment dimension left right =
      ∑ level ∈ Finset.range (left.card + right.card + 1),
        dimension.choose level * nilMoment level left right := by
  let count := left.card + right.card
  have hsplit : dimension + 1 = count + 1 + (dimension - count) := by omega
  rw [binomialMoment, hsplit, Finset.sum_range_add]
  have htail :
      (∑ offset ∈ Finset.range (dimension - count),
        dimension.choose (count + 1 + offset) *
          nilMoment (count + 1 + offset) left right) = 0 := by
    refine Finset.sum_eq_zero fun offset _ ↦ ?_
    rw [nilMoment_eq_zero_of_count_lt (count + 1 + offset) left right (by omega),
      Nat.mul_zero]
  rw [htail, Nat.add_zero]

/-- The independent-level reconstruction fold is the corresponding finite gated sum. -/
theorem nilMomentPairLevels_eq_sum
    (outWidth dimension maxLevel sigEnc : ℕ)
    (shifts pmasks widths masks : Lean.RArray ℕ)
    (trees : Lean.RArray (Lean.RArray ℕ)) (s t : ℕ) :
    cert246Data.nilMomentPairLevels outWidth dimension maxLevel sigEnc
        shifts pmasks widths masks trees s t =
      let count := cert246Data.sigCount (cert246Data.sigField sigEnc s) +
        cert246Data.sigCount (cert246Data.sigField sigEnc t)
      ∑ level ∈ Finset.range (Nat.min count maxLevel + 1),
        if count ≤ 2 * level then
          cert246Data.nilLevelAt shifts pmasks widths masks trees level
              (cert246Data.triIdx s t) *
            ((dimension - 1).choose level + (dimension.choose level).shiftLeft outWidth)
        else 0 := by
  unfold cert246Data.nilMomentPairLevels
  let count := cert246Data.sigCount (cert246Data.sigField sigEnc s) +
    cert246Data.sigCount (cert246Data.sigField sigEnc t)
  let value : ℕ → ℕ := fun level ↦
    cert246Data.nilLevelAt shifts pmasks widths masks trees level
        (cert246Data.triIdx s t) *
      ((dimension - 1).choose level + (dimension.choose level).shiftLeft outWidth)
  let used : ℕ → Bool := fun level ↦ Nat.ble count (2 * level)
  calc
    Nat.rec
        (fun _ accumulator ↦ accumulator)
        (fun _ inductionHypothesis level accumulator ↦
          inductionHypothesis level.succ
            (Bool.rec accumulator (accumulator + value level) (used level)))
        (Nat.min count maxLevel + 1) 0 0 =
      ∑ level ∈ Finset.range (Nat.min count maxLevel + 1),
        if used level = true then value level else 0 := by
      simpa only [Nat.zero_add] using
        gatedScan_sound used value (Nat.min count maxLevel + 1) 0 0
    _ = ∑ level ∈ Finset.range (Nat.min count maxLevel + 1),
        if count ≤ 2 * level then value level else 0 :=
      Finset.sum_congr rfl fun level _ ↦ by simp only [used, Nat.ble_eq]
    _ = _ := rfl

/-- A sound independently packed ladder reconstructs both requested ordinary moments. -/
theorem nilMomentPairLevels_sound
    {outWidth dimension maxLevel sigEnc : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} {s t : ℕ}
    (hcount : cert246Data.sigCount (cert246Data.sigField sigEnc s) +
        cert246Data.sigCount (cert246Data.sigField sigEnc t) =
      (sigOf sigEnc s).card + (sigOf sigEnc t).card)
    (hmax : (sigOf sigEnc s).card + (sigOf sigEnc t).card ≤ maxLevel)
    (hdimension : (sigOf sigEnc s).card + (sigOf sigEnc t).card ≤ dimension - 1)
    (hlookup : ∀ level ≤ (sigOf sigEnc s).card + (sigOf sigEnc t).card,
      Bool.rec (motive := fun _ ↦ ℕ) 0
        (cert246Data.nilLevelAt shifts pmasks widths masks trees level
          (cert246Data.triIdx s t))
        (cert246Data.nilActive level
          (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
            cert246Data.sigCount (cert246Data.sigField sigEnc t))) =
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t))
    (hzeroS : (0 : ℕ) ∉ sigOf sigEnc s) (hzeroT : (0 : ℕ) ∉ sigOf sigEnc t) :
    cert246Data.nilMomentPairLevels outWidth dimension maxLevel sigEnc
        shifts pmasks widths masks trees s t =
      facMomentNat (dimension - 1) (sigOf sigEnc s) (sigOf sigEnc t) +
        (facMomentNat dimension (sigOf sigEnc s) (sigOf sigEnc t)).shiftLeft outWidth := by
  let count := (sigOf sigEnc s).card + (sigOf sigEnc t).card
  rw [nilMomentPairLevels_eq_sum, hcount]
  dsimp only
  rw [Nat.min_eq_min, Nat.min_eq_left hmax]
  have hterms :
      (∑ level ∈ Finset.range (count + 1),
        if count ≤ 2 * level then
          cert246Data.nilLevelAt shifts pmasks widths masks trees level
              (cert246Data.triIdx s t) *
            ((dimension - 1).choose level + (dimension.choose level).shiftLeft outWidth)
        else 0) =
      ∑ level ∈ Finset.range (count + 1),
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t) *
          ((dimension - 1).choose level + (dimension.choose level).shiftLeft outWidth) := by
    refine Finset.sum_congr rfl fun level hlevel ↦ ?_
    have hlevelCount : level ≤ count := Nat.lt_succ_iff.mp (Finset.mem_range.mp hlevel)
    split_ifs with hactive
    · have hsupport : cert246Data.nilActive level
          (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
            cert246Data.sigCount (cert246Data.sigField sigEnc t)) = true := by
        unfold cert246Data.nilActive
        rw [Nat.ble_eq_true_of_le (by rw [hcount]; exact hlevelCount),
          Nat.ble_eq_true_of_le (by rw [hcount]; exact hactive)]
        rfl
      have hvalue := hlookup level hlevelCount
      rw [hsupport] at hvalue
      change cert246Data.nilLevelAt shifts pmasks widths masks trees level
          (cert246Data.triIdx s t) =
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t) at hvalue
      rw [hvalue]
    · rw [nilMoment_eq_zero_of_count_gt level (sigOf sigEnc s) (sigOf sigEnc t)
        (by simpa only [count] using Nat.lt_of_not_ge hactive), Nat.zero_mul]
  rw [hterms]
  have hsplit :
      (∑ level ∈ Finset.range (count + 1),
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t) *
          ((dimension - 1).choose level + (dimension.choose level).shiftLeft outWidth)) =
      (∑ level ∈ Finset.range (count + 1),
        (dimension - 1).choose level * nilMoment level (sigOf sigEnc s) (sigOf sigEnc t)) +
      (∑ level ∈ Finset.range (count + 1),
        dimension.choose level * nilMoment level (sigOf sigEnc s) (sigOf sigEnc t)
          ).shiftLeft outWidth :=
    calc
      _ = ∑ level ∈ Finset.range (count + 1),
          ((dimension - 1).choose level * nilMoment level (sigOf sigEnc s) (sigOf sigEnc t) +
            (dimension.choose level *
              nilMoment level (sigOf sigEnc s) (sigOf sigEnc t)).shiftLeft outWidth) := by
        refine Finset.sum_congr rfl fun level _ ↦ ?_
        simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq]
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib]
        congr 1
        simp only [Nat.shiftLeft_eq', Nat.shiftLeft_eq, Finset.sum_mul]
  rw [hsplit, ← binomialMoment_eq_sum_card (dimension - 1) _ _ hdimension,
    ← binomialMoment_eq_sum_card dimension _ _ (by omega),
    ← facMomentNat_eq_binomialMoment hzeroS hzeroT (dimension - 1),
    ← facMomentNat_eq_binomialMoment hzeroS hzeroT dimension]

end PrimeGaps.Gap246
