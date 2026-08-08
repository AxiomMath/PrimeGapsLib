/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Kernel.LHS
public import PrimeGapsCert.Gap246.Sums

import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring.RingNF

/-! # Soundness of the two-lane signed-natural representation -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Interpret the low sign bit and remaining magnitude as an integer. -/
noncomputable def signedValue (value : ℕ) : ℤ :=
  if cert246Data.signedSign value = 0 then cert246Data.signedMagnitude value
  else -cert246Data.signedMagnitude value

/-- The stored sign bit is the parity bit. -/
theorem signedSign_eq_mod (value : ℕ) :
    cert246Data.signedSign value = value % 2 := by
  unfold cert246Data.signedSign
  convert Nat.and_two_pow_sub_one_eq_mod value 1 using 1
  all_goals norm_num

/-- The stored sign bit is a single bit. -/
theorem signedSign_lt_two (value : ℕ) : cert246Data.signedSign value < 2 := by
  rw [signedSign_eq_mod]
  exact Nat.mod_lt _ (by norm_num)

private theorem signedMagnitude_eq_div (value : ℕ) :
    cert246Data.signedMagnitude value = value / 2 := by
  unfold cert246Data.signedMagnitude
  convert Nat.shiftRight_eq_div_pow value 1 using 1
  all_goals norm_num

/-- Normalizing two natural lanes represents their integer difference. -/
theorem signedValue_encode (positive negative : ℕ) :
    signedValue (cert246Data.signedEncode positive negative) =
      (positive : ℤ) - negative := by
  rw [cert246Data.signedEncode]
  by_cases h : negative ≤ positive
  · have hbool : Nat.ble negative positive = true := Nat.ble_eq.mpr h
    rw [hbool]
    simp [signedValue, signedSign_eq_mod, signedMagnitude_eq_div, Nat.shiftLeft_eq]
    omega
  · have hbool : Nat.ble negative positive = false :=
      Bool.eq_false_of_not_eq_true fun htrue ↦ h (Nat.ble_eq.mp htrue)
    rw [hbool]
    simp [signedValue, signedSign_eq_mod, signedMagnitude_eq_div, Nat.shiftLeft_eq]
    omega

/-- A first-order two-lane scan represents the corresponding signed integer sum. -/
theorem signedRec_sound (positive : ℕ → Bool) (term : ℕ → ℕ) :
    ∀ count cursor initialPositive initialNegative,
      signedValue
          (Nat.rec (motive := fun _ ↦ ℕ → ℕ → ℕ → ℕ)
            (fun _ positiveLane negativeLane ↦
              cert246Data.signedEncode positiveLane negativeLane)
            (fun _ inductionHypothesis cursor' positiveLane negativeLane ↦
              Bool.rec
                (inductionHypothesis cursor'.succ positiveLane
                  (negativeLane + term cursor'))
                (inductionHypothesis cursor'.succ
                  (positiveLane + term cursor') negativeLane)
                (positive cursor'))
            count cursor initialPositive initialNegative) =
        (initialPositive : ℤ) - initialNegative +
          ∑ offset ∈ Finset.range count,
            if positive (cursor + offset) = true then (term (cursor + offset) : ℤ)
            else -(term (cursor + offset) : ℤ) := by
  intro count
  induction count with
  | zero =>
      intro cursor initialPositive initialNegative
      rw [Nat.rec_zero, signedValue_encode]
      simp
  | succ count inductionHypothesis =>
      intro cursor initialPositive initialNegative
      dsimp only
      rw [sum_range_head
        (fun index ↦ if positive index = true then (term index : ℤ) else -(term index : ℤ))
        cursor count]
      rcases hpositive : positive cursor with _ | _ <;>
        simp only [Bool.false_eq_true, ↓reduceIte] <;>
          rw [inductionHypothesis] <;> push_cast <;> ring

/-- A successful first-order Boolean scan certifies every index in its interval. -/
theorem boolRec_sound (check : ℕ → Bool) : ∀ count cursor,
    Nat.rec (motive := fun _ ↦ ℕ → Bool)
        (fun _ ↦ true)
        (fun _ inductionHypothesis index ↦
          Bool.rec false (inductionHypothesis index.succ) (check index))
        count cursor = true →
      ∀ index, cursor ≤ index → index < cursor + count → check index = true := by
  intro count
  induction count with
  | zero =>
      intro cursor _ index _ hupper
      omega
  | succ count inductionHypothesis =>
      intro cursor hscan index hlower hupper
      dsimp only at hscan
      rcases hcheck : check cursor with _ | _
      · simp [hcheck] at hscan
      · rw [hcheck] at hscan
        rcases Nat.eq_or_lt_of_le hlower with rfl | hlower
        · exact hcheck
        · exact inductionHypothesis cursor.succ hscan index (by omega) (by omega)

/-- Multiplying one packed signed value by a natural respects its sign and magnitude. -/
theorem signedScaleTerm (value factor : ℕ) :
    (if cert246Data.signedSign value = 0 then
        (cert246Data.signedMagnitude value * factor : ℤ)
      else -(cert246Data.signedMagnitude value * factor : ℤ)) =
      signedValue value * factor := by
  unfold signedValue
  split <;> ring

/-- Natural multiplication before casting gives the same signed scaling. -/
theorem signedScaleTermNat (value factor : ℕ) :
    (if cert246Data.signedSign value = 0 then
        ((cert246Data.signedMagnitude value * factor : ℕ) : ℤ)
      else -((cert246Data.signedMagnitude value * factor : ℕ) : ℤ)) =
      signedValue value * Int.ofNat factor := by
  push_cast
  exact signedScaleTerm value factor

/-- The equality of two packed sign bits determines the sign of their magnitude product. -/
theorem signedProductTerm (left right : ℕ) :
    (if cert246Data.signedSign left = cert246Data.signedSign right then
        (cert246Data.signedMagnitude left * cert246Data.signedMagnitude right : ℤ)
      else
        -(cert246Data.signedMagnitude left * cert246Data.signedMagnitude right : ℤ)) =
      signedValue left * signedValue right := by
  have hleft := signedSign_lt_two left
  have hright := signedSign_lt_two right
  interval_cases hleftSign : cert246Data.signedSign left <;>
    interval_cases hrightSign : cert246Data.signedSign right <;>
      simp [signedValue, hleftSign, hrightSign]

end PrimeGaps.Gap246
