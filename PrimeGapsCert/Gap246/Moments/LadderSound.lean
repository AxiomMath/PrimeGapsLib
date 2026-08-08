/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.TableSound

/-! # Soundness of the nilpotent moment ladder -/

@[expose] public section

open scoped Nat

namespace PrimeGaps.Gap246

open Finset

/-! ## Symmetry and decoding -/

/-- The identity-free transition preserves symmetry of the moment state. -/
theorem nilStep_comm (state : MomentState)
    (hstate : ∀ left right, state left right = state right left) (left right : Multiset ℕ) :
    nilStep state left right = nilStep state right left := by
  have hright :
      (∑ y ∈ right.toFinset, y ! * state left (right.erase y)) =
        ∑ y ∈ right.toFinset, y ! * state (right.erase y) left :=
    Finset.sum_congr rfl fun y _ ↦ by rw [hstate left (right.erase y)]
  have hleft :
      (∑ x ∈ left.toFinset, x ! * state (left.erase x) right) =
        ∑ x ∈ left.toFinset, x ! * state right (left.erase x) :=
    Finset.sum_congr rfl fun x _ ↦ by rw [hstate (left.erase x) right]
  have hcross :
      (∑ x ∈ left.toFinset, ∑ y ∈ right.toFinset,
        (x + y) ! * state (left.erase x) (right.erase y)) =
      ∑ y ∈ right.toFinset, ∑ x ∈ left.toFinset,
        (y + x) ! * state (right.erase y) (left.erase x) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun y _ ↦ Finset.sum_congr rfl fun x _ ↦ by
      rw [Nat.add_comm, hstate (left.erase x) (right.erase y)]
  unfold nilStep
  simp only [Finset.sum_add_distrib]
  rw [hright, hleft, hcross]
  ac_rfl

/-- Every nilpotent level is symmetric in its two signatures. -/
theorem nilMoment_comm : ∀ level (left right : Multiset ℕ),
    nilMoment level left right = nilMoment level right left
  | 0, left, right => by
      simp [nilMoment, nilBase, and_comm]
  | level + 1, left, right => by
      simpa only [nilMoment_succ] using
        nilStep_comm (nilMoment level) (nilMoment_comm level) left right

/-- The decoded signature cardinality is the count nibble in its packed field. -/
theorem sigOf_card (sigEnc row : ℕ) :
    (sigOf sigEnc row).card =
      cert246Data.sigCount (cert246Data.sigField sigEnc row) := by
  rw [sigOf, decodeSig_eq_map]
  simp

private theorem land_fifteen (x : ℕ) : Nat.land x 15 = x % 16 :=
  Nat.and_two_pow_sub_one_eq_mod x 4

private theorem sigCount_eq_mod (enc : ℕ) : cert246Data.sigCount enc = enc % 16 :=
  land_fifteen enc

private theorem sigNib_eq_div (enc position : ℕ) :
    cert246Data.sigNib enc position = enc / 2 ^ (4 * (position + 1)) % 16 := by
  unfold cert246Data.sigNib
  rw [land_fifteen]
  simp [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]

private theorem eq_zero_of_nibbles_zero : ∀ count value : ℕ,
    value < 2 ^ (4 * count) →
    (∀ position < count, value / 2 ^ (4 * position) % 16 = 0) → value = 0 := by
  intro count
  induction count with
  | zero => exact fun value hvalue _ ↦ by simpa using hvalue
  | succ count inductionHypothesis =>
      intro value hvalue hnibble
      have hpower : (2 : ℕ) ^ (4 * (count + 1)) = 16 * 2 ^ (4 * count) := by ring
      have hzero : value % 16 = 0 := by simpa using hnibble 0 (by omega)
      have hquotient := inductionHypothesis (value / 16) (by omega) fun position hposition ↦ by
        rw [Nat.div_div_eq_div_mul,
          (by ring : (16 : ℕ) * 2 ^ (4 * position) = 2 ^ (4 * (position + 1)))]
        exact hnibble (position + 1) (by omega)
      omega

/-- A checked packed signature field is zero exactly when its decoded signature is empty. -/
theorem sigOf_eq_zero_iff {S maxNib sigEnc eraseEnc row enc count : ℕ}
    (hrow : RowFacts S maxNib sigEnc eraseEnc row enc count)
    (hcount : count = cert246Data.sigCount enc)
    (hfield : cert246Data.sigField sigEnc row = enc)
    (hbound : enc < 2 ^ (4 * (maxNib + 1))) :
    sigOf sigEnc row = 0 ↔ cert246Data.sigField sigEnc row = 0 := by
  rw [sigOf, hfield]
  constructor
  · intro hdecode
    have hempty : cert246Kernel.decodeSig enc = 0 := hdecode
    rw [decodeSig_eq_map, Multiset.coe_eq_zero, List.map_eq_nil_iff,
      List.range_eq_nil] at hempty
    exact eq_zero_of_nibbles_zero (maxNib + 1) enc hbound fun position hposition ↦ by
      rcases position with _ | position
      · simpa [← sigCount_eq_mod] using hempty
      · rw [← sigNib_eq_div]
        exact hrow.nib_zero position (by omega) (by omega)
  · intro hzero
    rw [hzero]
    simp [decodeSig_eq_map, sigCount_eq_mod]

/-! ## The checked ladder -/

/-- Soundness of a nilpotent ladder whose levels are packed independently. -/
theorem nilLevelLadder_sound
    {S maxNib partBound sigEnc eraseEnc factT lastLevel : ℕ}
    {shifts pmasks widths masks : Lean.RArray ℕ}
    {trees : Lean.RArray (Lean.RArray ℕ)} (hS : S ≤ 512)
    (hrows : ∀ row < S, RowFacts S maxNib sigEnc eraseEnc row
      (cert246Data.sigField sigEnc row)
      (cert246Data.sigCount (cert246Data.sigField sigEnc row)))
    (hencoding : ∀ row < S,
      cert246Data.sigField sigEnc row < 2 ^ (4 * (maxNib + 1)))
    (hpart : ∀ row < S, ∀ position < maxNib,
      cert246Data.sigNib (cert246Data.sigField sigEnc row) position ≤ partBound)
    (hfactorial : ∀ n ≤ 4 * partBound,
      cert246Data.factAt factT n = n !)
    (hbase : ∀ t < S, ∀ s ≤ t,
      cert246Data.nilLevelAt shifts pmasks widths masks trees 0
          (cert246Data.triIdx s t) =
        if cert246Data.sigField sigEnc s = 0 ∧
            cert246Data.sigField sigEnc t = 0 then 1 else 0)
    (hstep : ∀ level, 0 < level → level ≤ lastLevel → ∀ t < S, ∀ s ≤ t,
      let active := cert246Data.nilActive level
        (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField sigEnc t))
      Bool.rec (motive := fun _ ↦ ℕ) 0
          (cert246Data.nilLevelAt shifts pmasks widths masks trees level
          (cert246Data.triIdx s t)) active =
        Bool.rec (motive := fun _ ↦ ℕ) 0
          (cert246Data.nilLevelEntry sigEnc eraseEnc factT level
          shifts pmasks widths masks trees s t) active) :
    ∀ level ≤ lastLevel, ∀ t < S, ∀ s ≤ t,
      Bool.rec (motive := fun _ ↦ ℕ) 0
          (cert246Data.nilLevelAt shifts pmasks widths masks trees level
          (cert246Data.triIdx s t))
        (cert246Data.nilActive level
          (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
            cert246Data.sigCount (cert246Data.sigField sigEnc t))) =
        nilMoment level (sigOf sigEnc s) (sigOf sigEnc t) := by
  intro level
  induction level with
  | zero =>
      intro _ t ht s hst
      rw [hbase t ht s hst]
      simp only [nilMoment, pow_zero, AddMonoid.End.one_apply, nilBase]
      have hszero := sigOf_eq_zero_iff (hrows s (by omega)) rfl rfl
        (hencoding s (by omega))
      have htzero := sigOf_eq_zero_iff (hrows t ht) rfl rfl (hencoding t ht)
      simp only [hszero, htzero]
      by_cases hzero : cert246Data.sigField sigEnc s = 0 ∧
          cert246Data.sigField sigEnc t = 0
      · change cert246Data.sigField sigEnc s = 0 ∧ cert246Data.sigField sigEnc t = 0 at hzero
        have hactive : cert246Data.nilActive 0
            (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
              cert246Data.sigCount (cert246Data.sigField sigEnc t)) = true := by
          rw [hzero.1, hzero.2]
          rfl
        simp only [hactive]
      · have hcount : 0 < cert246Data.sigCount (cert246Data.sigField sigEnc s) +
            cert246Data.sigCount (cert246Data.sigField sigEnc t) := by
          by_contra hnot
          have hsum : cert246Data.sigCount (cert246Data.sigField sigEnc s) +
              cert246Data.sigCount (cert246Data.sigField sigEnc t) = 0 := by omega
          obtain ⟨hsCount, htCount⟩ := Nat.add_eq_zero_iff.mp hsum
          have hsEmpty : sigOf sigEnc s = 0 := Multiset.card_eq_zero.mp (by
            simpa only [sigOf_card] using hsCount)
          have htEmpty : sigOf sigEnc t = 0 := Multiset.card_eq_zero.mp (by
            simpa only [sigOf_card] using htCount)
          exact hzero ⟨hszero.mp hsEmpty, htzero.mp htEmpty⟩
        change ¬(cert246Data.sigField sigEnc s = 0 ∧ cert246Data.sigField sigEnc t = 0) at hzero
        rw [if_neg hzero]
        change 0 < cert246Data.sigCount (cert246Data.sigField sigEnc s) +
          cert246Data.sigCount (cert246Data.sigField sigEnc t) at hcount
        have hactive : cert246Data.nilActive 0
            (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
              cert246Data.sigCount (cert246Data.sigField sigEnc t)) = false := by
          unfold cert246Data.nilActive
          rw [Nat.ble_eq_true_of_le (Nat.zero_le _)]
          simp only [Bool.and'_eq_and, Bool.true_and]
          cases hble : Nat.ble
              (cert246Data.sigCount (cert246Data.sigField sigEnc s) +
                cert246Data.sigCount (cert246Data.sigField sigEnc t)) 0 with
          | false => rfl
          | true =>
              have hle := Nat.le_of_ble_eq_true hble
              omega
        simp only [hactive]
  | succ previous inductionHypothesis =>
      intro hlevel t ht s hst
      have hs : s < S := by omega
      have hlookup : ∀ first < S, ∀ second < S,
          cert246Data.nilLevelPreviousAt sigEnc previous shifts pmasks widths masks trees
              first second =
            nilMoment previous (sigOf sigEnc first) (sigOf sigEnc second) := by
        intro first hfirst second hsecond
        rcases Nat.le_total first second with horder | horder
        · simpa only [cert246Data.nilLevelPreviousAt, Nat.add_eq] using
            inductionHypothesis (by omega) second hsecond first horder
        · simpa only [cert246Data.nilLevelPreviousAt, Nat.add_eq, triIdx_comm, Nat.add_comm,
            nilMoment_comm] using
            inductionHypothesis (by omega) first hfirst second horder
      have hentry :
          cert246Data.nilLevelEntry sigEnc eraseEnc factT (previous + 1)
              shifts pmasks widths masks trees s t =
            nilStep (nilMoment previous) (sigOf sigEnc s) (sigOf sigEnc t) := by
        unfold cert246Data.nilLevelEntry
        rw [nilEntryWith_eq_nilRowValWith]
        exact nilRowValWith_eq_nilStep hS hs ht hrows hpart hfactorial (by
          simpa only [Nat.sub_eq, Nat.add_sub_cancel] using hlookup)
      let count := cert246Data.sigCount (cert246Data.sigField sigEnc s) +
        cert246Data.sigCount (cert246Data.sigField sigEnc t)
      have hchecked := hstep (previous + 1) (by omega) hlevel t ht s hst
      change Bool.rec (motive := fun _ ↦ ℕ) 0
          (cert246Data.nilLevelAt shifts pmasks widths masks trees (previous + 1)
            (cert246Data.triIdx s t))
          (cert246Data.nilActive (previous + 1) count) =
        Bool.rec (motive := fun _ ↦ ℕ) 0
          (cert246Data.nilLevelEntry sigEnc eraseEnc factT (previous + 1)
            shifts pmasks widths masks trees s t)
          (cert246Data.nilActive (previous + 1) count) at hchecked
      rcases hactive : cert246Data.nilActive (previous + 1) count with _ | _
      · change 0 = nilMoment (previous + 1) (sigOf sigEnc s) (sigOf sigEnc t)
        symm
        have hcard : (sigOf sigEnc s).card + (sigOf sigEnc t).card = count := by
          simp only [sigOf_card, count]
        by_cases hlower : previous + 1 ≤ count
        · have hupper : 2 * (previous + 1) < count := by
            by_contra hnot
            have hle : count ≤ 2 * (previous + 1) := by omega
            have htrue : cert246Data.nilActive (previous + 1) count = true := by
              simp [cert246Data.nilActive, hlower, hle]
            rw [htrue] at hactive
            simp at hactive
          exact nilMoment_eq_zero_of_count_gt (previous + 1)
            (sigOf sigEnc s) (sigOf sigEnc t) (by omega)
        · exact nilMoment_eq_zero_of_count_lt (previous + 1)
            (sigOf sigEnc s) (sigOf sigEnc t) (by omega)
      · simp only [hactive] at hchecked
        change cert246Data.nilLevelAt shifts pmasks widths masks trees (previous + 1)
            (cert246Data.triIdx s t) =
          nilMoment (previous + 1) (sigOf sigEnc s) (sigOf sigEnc t)
        exact hchecked.trans (hentry.trans (congrFun
          (congrFun (nilMoment_succ previous) (sigOf sigEnc s)) (sigOf sigEnc t)).symm)

end PrimeGaps.Gap246
