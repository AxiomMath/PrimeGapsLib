/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Data.FinEnum
public import Mathlib.Data.Finset.Sort
public import Mathlib.Tactic.IntervalCases

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Admissibility of a set of natural numbers

## Main definitions

* `Finset.Admissible`: `S : Finset ℕ` is said to be admissible if, across `n : ℕ`, the products
  `∏ i ∈ S, (n + i)` have no fixed prime divisor. This is a central idea in the study of bounded
  gaps between primes. We make a `Decidable` instance for it in this file.
* `Finset.diameter`: the difference between the largest and the smallest element of a finite set.

## Main results

* `Finset.admissible_iff_le_card`: admissibility reduces to a finite check over the primes
  `p ≤ #H`.
* `PrimeGaps.admissible_H105`: `PrimeGaps.H105` is an admissible 105-tuple of diameter 600.
-/

@[expose] public section

namespace Finset

/-- A finite set `H` of natural numbers is *admissible* if, for every prime `p`,
there exists a residue class `a : ZMod p` which is missed by the image of `H` in
`ZMod p`. -/
@[pg_tag "bg246" "def_admissible"]
def Admissible (H : Finset ℕ) : Prop := ∀ p : ℕ, p.Prime → ∃ a : ℕ, ∀ h ∈ H, ¬ (h ≡ a [MOD p])

lemma admissible_def (H : Finset ℕ) :
    H.Admissible ↔ ∀ p : ℕ, p.Prime → ∃ a : ℕ, ∀ h ∈ H, ¬ (h ≡ a [MOD p]) := .rfl

lemma admissible_iff_forall_prime_exists_lt_forall_not_modEq (H : Finset ℕ) : H.Admissible ↔
    ∀ p : ℕ, p.Prime → ∃ a < p, ∀ h ∈ H, ¬ (h ≡ a [MOD p]) := by
  rw [admissible_def]
  refine ⟨fun hyp p hp ↦ ?_, fun hyp p hp ↦ (hyp p hp).imp fun _ ha ↦ ha.2⟩
  obtain ⟨a, ha⟩ := hyp p hp
  exact ⟨a % p, Nat.mod_lt _ hp.pos, fun h hh hmod ↦ ha h hh (hmod.trans (Nat.mod_modEq a p))⟩

theorem Admissible.exists_lt_forall_not_modEq {H : Finset ℕ} (h : H.Admissible)
    {p : ℕ} (hp : p.Prime) : ∃ a < p, ∀ h ∈ H, ¬ (h ≡ a [MOD p]) :=
  (admissible_iff_forall_prime_exists_lt_forall_not_modEq H).mp h p hp

lemma admissible_iff_forall_prime_exists_lt_mod_ne (H : Finset ℕ) : H.Admissible ↔
    ∀ p : ℕ, p.Prime → ∃ a < p, ∀ h ∈ H, h % p ≠ a := by
  rw [admissible_iff_forall_prime_exists_lt_forall_not_modEq]
  exact forall₂_congr fun p hp ↦ exists_congr fun a ↦ by grind [Nat.ModEq, Nat.mod_eq_of_lt]

lemma admissible_iff_forall_prime_exists_ZMod_nequiv (H : Finset ℕ) : H.Admissible ↔
    ∀ p : ℕ, p.Prime → ∃ a : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ a := by
  simp_rw [admissible_def, ← ZMod.natCast_eq_natCast_iff]
  refine forall₂_congr fun p hp ↦ ?_
  have := NeZero.mk hp.ne_zero
  rw [(ZMod.natCast_zmod_surjective (n := p)).exists]

/-- Any subset of an admissible finset is admissible. -/
theorem Admissible.subset {H₂ : Finset ℕ} (hH₂ : H₂.Admissible) {H₁ : Finset ℕ}
    (hsub : H₁ ⊆ H₂) : H₁.Admissible := fun p hp ↦
  (hH₂ p hp).imp fun _ ha h hh ↦ ha h (hsub hh)

/-- The diameter of a finite set `H` of natural numbers is the difference between its largest and
smallest elements. -/
@[pg_tag "bg246" "def_diam"]
def diameter (H : Finset ℕ) : ℕ := H.sup id - H.min.getD 0

/-- For `𝓗 = {h₁ < ⋯ < h_k}`, `diam(𝓗) = h_k − h₁`. -/
@[pg_tag "bg246" "lem_diam_max_min"]
theorem diameter_eq_max_sub_min {H : Finset ℕ} (h : H.Nonempty) :
    H.diameter = H.max' h - H.min' h := by
  rw [diameter, ← sup'_eq_sup h, ← max'_eq_sup' H h, ← coe_min' h]
  norm_cast

section ReductionAndDecidability

/-- **Reduction lemma.** If a set of natural numbers has cardinality less than a prime `p`, then it
misses some residue class modulo `p`. -/
theorem exists_lt_forall_mod_ne_of_card_lt {H : Finset ℕ} {p : ℕ}
    (hpk : #H < p) : ∃ a < p, ∀ h ∈ H, h % p ≠ a := by
  have := NeZero.mk (n := p) (by grind)
  have himg : #(H.image ((↑) : ℕ → ZMod p)) < #(univ : Finset (ZMod p)) := by
    rw [card_univ, ZMod.card]
    exact card_image_le.trans_lt hpk
  obtain ⟨a, -, ha⟩ := exists_mem_notMem_of_card_lt_card himg
  refine ⟨a.val, a.val_lt, fun h hh heq ↦ ha (mem_image.mpr ⟨h, hh, ?_⟩)⟩
  rwa [← (ZMod.val_injective p).eq_iff, ZMod.val_natCast]

/-- **Reduction to a finite check.** Admissibility of `H : Finset ℕ` is equivalent to the bounded
condition that for each prime `p ≤ #H` some residue class mod `p` is missed by `H`. The reduction
uses `Finset.exists_lt_forall_mod_ne_of_card_lt` to handle primes `p > H.card` automatically. -/
@[pg_tag "bg246" "lem_adm_small_primes"]
theorem admissible_iff_le_card (H : Finset ℕ) :
    H.Admissible ↔ ∀ p ≤ #H, p.Prime → ∃ a < p, ∀ x ∈ H, x % p ≠ a := by
  rw [admissible_iff_forall_prime_exists_lt_mod_ne]
  refine ⟨fun hadm _ _ hp ↦ hadm _ hp, fun h p hp ↦ ?_⟩
  by_cases hpcard : #H < p
  · exact exists_lt_forall_mod_ne_of_card_lt hpcard
  · exact h p (not_lt.mp hpcard) hp

instance instDecidablePredAdmissible : DecidablePred Admissible :=
  fun H ↦ decidable_of_iff' _ (admissible_iff_le_card H)

end ReductionAndDecidability

end Finset

open Finset

namespace PrimeGaps

/-- The set `{0, 2, 6, 8, 12}`. -/
def H5 : Finset ℕ := {0, 2, 6, 8, 12}

@[simp] theorem admissible_H5 : H5.Admissible := by decide

@[simp] theorem diameter_H5 : H5.diameter = 12 := rfl

@[simp] theorem card_H5 : #H5 = 5 := rfl

/-- An admissible 105-tuple of diameter 600. It is optimal for length 105. -/
def H105 : Finset ℕ :=
  {0, 10, 12, 24, 28, 30, 34, 42, 48, 52, 54, 64, 70, 72, 78,
  82, 90, 94, 100, 112, 114, 118, 120, 124, 132, 138, 148, 154, 168, 174, 178, 180, 184, 190, 192,
  202, 204, 208, 220, 222, 232, 234, 250, 252, 258, 262, 264, 268, 280, 288, 294, 300, 310, 322,
  324, 328, 330, 334, 342, 352, 358, 360, 364, 372, 378, 384, 390, 394, 400, 402, 408, 412, 418,
  420, 430, 432, 442, 444, 450, 454, 462, 468, 472, 478, 484, 490, 492, 498, 504, 510, 528, 532,
  534, 538, 544, 558, 562, 570, 574, 580, 582, 588, 594, 598, 600}

@[pg_tag "bg246" "thm_engelsma", simp]
theorem admissible_H105 : H105.Admissible := by set_option maxRecDepth 1184 in decide

set_option maxRecDepth 1500 in
@[pg_tag "bg246" "thm_engelsma", simp]
theorem diameter_H105 : H105.diameter = 600 := rfl

set_option maxRecDepth 1500 in
@[pg_tag "bg246" "thm_engelsma", simp]
theorem card_H105 : #H105 = 105 := rfl

end PrimeGaps
