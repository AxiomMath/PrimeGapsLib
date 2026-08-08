/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsCert.Gap246.Moments.CheckSound

/-! # Support bounds for the nilpotent moment ladder -/

@[expose] public section

namespace PrimeGaps.Gap246

open Finset

/-- Successive nilpotent levels are obtained by applying the identity-free transition. -/
theorem nilMoment_succ (level : ℕ) : nilMoment (level + 1) = nilStep (nilMoment level) := by
  funext α β
  unfold nilMoment
  rw [pow_succ',
    congrFun (AddMonoid.End.coe_mul MomentState nilOperator (nilOperator ^ level)) nilBase,
    Function.comp_apply]
  rfl

/-- A genuine erasure reduces the cardinality by one. -/
private theorem card_erase_one {signature : Multiset ℕ} {part : ℕ}
    (hpart : part ∈ signature) : (signature.erase part).card + 1 = signature.card := by
  rw [Multiset.card_erase_of_mem hpart]
  simpa [Nat.succ_eq_add_one] using
    Nat.succ_pred_eq_of_pos (Multiset.card_pos_iff_exists_mem.mpr ⟨part, hpart⟩)

/-- Level `level + 1` vanishes as soon as level `level` vanishes on every pair reachable by
erasing one part from either side. -/
private theorem nilMoment_succ_eq_zero {level : ℕ} {α β : Multiset ℕ}
    (hα : ∀ x ∈ α.toFinset, nilMoment level (α.erase x) β = 0)
    (hβ : ∀ y ∈ β.toFinset, nilMoment level α (β.erase y) = 0)
    (hαβ : ∀ x ∈ α.toFinset, ∀ y ∈ β.toFinset,
      nilMoment level (α.erase x) (β.erase y) = 0) :
    nilMoment (level + 1) α β = 0 := by
  rw [nilMoment_succ, nilStep]
  refine Nat.add_eq_zero_iff.mpr
    ⟨Finset.sum_eq_zero fun y hy ↦ ?_, Finset.sum_eq_zero fun x hx ↦ ?_⟩
  · rw [hβ y hy, Nat.mul_zero]
  · rw [hα x hx, Nat.mul_zero, Nat.zero_add]
    exact Finset.sum_eq_zero fun y hy ↦ by rw [hαβ x hx y hy, Nat.mul_zero]

/-- The cardinality of an erasure of a member of `α.toFinset`. -/
private theorem card_erase_toFinset {α : Multiset ℕ} {x : ℕ} (hx : x ∈ α.toFinset) :
    (α.erase x).card + 1 = α.card :=
  card_erase_one (Multiset.mem_toFinset.mp hx)

/-- Level `r` vanishes on pairs containing fewer than `r` parts in total. -/
theorem nilMoment_eq_zero_of_count_lt : ∀ level (α β : Multiset ℕ),
    α.card + β.card < level → nilMoment level α β = 0 := by
  intro level
  induction level with
  | zero => exact fun _ _ h ↦ absurd h (Nat.not_lt_zero _)
  | succ level inductionHypothesis =>
      intro α β hcount
      exact nilMoment_succ_eq_zero
        (fun x hx ↦ inductionHypothesis _ _ (by have := card_erase_toFinset hx; omega))
        (fun y hy ↦ inductionHypothesis _ _ (by have := card_erase_toFinset hy; omega))
        (fun x hx y hy ↦ inductionHypothesis _ _ (by
          have hxc := card_erase_toFinset hx
          have hyc := card_erase_toFinset hy
          omega))

/-- Level `r` vanishes on pairs containing more than `2r` parts in total. -/
theorem nilMoment_eq_zero_of_count_gt : ∀ level (α β : Multiset ℕ),
    2 * level < α.card + β.card → nilMoment level α β = 0 := by
  intro level
  induction level with
  | zero =>
      intro α β hcount
      simp only [nilMoment, pow_zero, AddMonoid.End.one_apply, nilBase]
      by_cases hzero : α = 0 ∧ β = 0
      · obtain ⟨rfl, rfl⟩ := hzero
        simp at hcount
      · simp [hzero]
  | succ level inductionHypothesis =>
      intro α β hcount
      exact nilMoment_succ_eq_zero
        (fun x hx ↦ inductionHypothesis _ _ (by have := card_erase_toFinset hx; omega))
        (fun y hy ↦ inductionHypothesis _ _ (by have := card_erase_toFinset hy; omega))
        (fun x hx y hy ↦ inductionHypothesis _ _ (by
          have hxc := card_erase_toFinset hx
          have hyc := card_erase_toFinset hy
          omega))

end PrimeGaps.Gap246
