/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Sparse.WeightCore


/-! # Digit reconstruction for carry-free packed RHS weights -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Reindex a rectangular shifted sum as one carry-free lane code. -/
theorem rhsShiftedSum_eq_laneCode (outerCount innerCount featureCount laneWidth : ℕ)
    (enabled : ℕ → ℕ → Bool) (location magnitude : ℕ → ℕ → ℕ)
    (hlocation : ∀ outer < outerCount, ∀ inner < innerCount,
      enabled outer inner = true → location outer inner < featureCount) :
    (∑ outer ∈ Finset.range outerCount, ∑ inner ∈ Finset.range innerCount,
        if enabled outer inner = true then
          Nat.shiftLeft (magnitude outer inner) (laneWidth * location outer inner)
        else 0) =
      rhsWeightLaneCode (2 ^ laneWidth) (fun (feature : Fin featureCount) ↦
        ∑ outer ∈ Finset.range outerCount, ∑ inner ∈ Finset.range innerCount,
          if enabled outer inner = true ∧ location outer inner = feature.val then
            magnitude outer inner
          else 0) := by
  symm
  unfold rhsWeightLaneCode
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro outer houter
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro inner hinner
  by_cases henabled : enabled outer inner = true
  · have hlocation' := hlocation outer (Finset.mem_range.mp houter) inner
      (Finset.mem_range.mp hinner) henabled
    let feature : Fin featureCount := ⟨location outer inner, hlocation'⟩
    rw [Finset.sum_eq_single feature]
    · simp only [henabled, true_and, if_true, feature]
      symm
      rw [Nat.shiftLeft_eq', Nat.shiftLeft_eq, pow_mul]
    · intro other _ hne
      have hvalue : location outer inner ≠ other.val := by
        intro heq
        exact hne (Fin.ext heq.symm)
      simp [hvalue]
    · simp
  · simp [henabled]

/-- Every source digit is bounded by the total active source magnitude. -/
theorem certRhsSourceDigit_le_bound (positive : Bool) (feature : Fin certRhsFeatureCount) :
    certRhsSourceDigit positive feature ≤ certRhsSourceBound := by
  unfold certRhsSourceDigit certRhsSourceBound
  apply Finset.sum_le_sum
  intro label hlabel
  apply Finset.sum_le_sum
  intro exponent hexponent
  by_cases hselected : certRhsActive label exponent = true ∧
      (certRhsSign label = 0) = (positive = true) ∧
      certRhsSourceLocation label exponent = feature.val
  · rw [if_pos hselected, if_pos hselected.1]
  · rw [if_neg hselected]
    exact Nat.zero_le _

/-- The two unsigned source digits at one feature are their direct signed rectangular sum. -/
theorem certRhsSourceDigit_sub (feature : Fin certRhsFeatureCount) :
    (certRhsSourceDigit true feature : ℤ) - certRhsSourceDigit false feature =
      ∑ label ∈ Finset.range certRhsLabelCount,
        ∑ exponent ∈ Finset.range (certRhsDegreeBound + 1),
          if certRhsActive label exponent = true ∧
              certRhsSourceLocation label exponent = feature.val then
            if certRhsSign label = 0 then (certRhsMagnitude label exponent : ℤ)
            else -(certRhsMagnitude label exponent : ℤ)
          else 0 := by
  unfold certRhsSourceDigit
  push_cast
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro label hlabel
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro exponent hexponent
  by_cases hactive : certRhsActive label exponent = true
  · by_cases hlocation : certRhsSourceLocation label exponent = feature.val
    · by_cases hsign : certRhsSign label = 0 <;> simp [hactive, hlocation, hsign]
    · simp [hactive, hlocation]
  · simp [hactive]

end PrimeGaps.Gap246
