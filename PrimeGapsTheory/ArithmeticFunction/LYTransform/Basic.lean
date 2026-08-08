/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.FunctionG
public import PrimeGapsTheory.Sieve.PermissibleSupport.Basic

import PrimeGapsTheory.ForMathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeGapsTheory.Tactic.PaperTag

/-!
# The `y` variables

Given a weight function `l : ℕᵏ → ℝ` (typically the sieve weights `λ_{d₁,⋯,dₖ}` from
`PrimeGapsTheory.ArithmeticFunction.LYTransform.Specialized`), this file defines the
associated variables `y_{r₁,⋯,rₖ}`.

## Main definitions

* `PrimeGaps.lToY`: the variable `y_r = (∏ᵢ μ(rᵢ) φ(rᵢ)) · ∑_d λ_d / ∏ᵢ dᵢ`.
* `PrimeGaps.yToL`: the reverse correspondence `λ_d = (∏ᵢ, μ(dᵢ) dᵢ) * ∑_r y_r / ∏ᵢ, φ(rᵢ)`.
* `PrimeGaps.ym`: a variable similar to `y` but with `d_m = 1` for fixed `m`.
-/

@[expose] public section

open Nat Finset Finsupp
open ArithmeticFunction Moebius detotient

namespace PrimeGaps

variable {R W k : ℕ} {m : Fin k} {l y : (Fin k → ℕ) →₀ ℝ} {d r : Fin k → ℕ} {c : ℝ}

/-- The linear map from the sieve coefficients `l` to their transformed coefficients. -/
@[pg_tag "bg246" "def_y_from_lambda", pg_tag "bg246" "def_y_vars"]
noncomputable def lToY {k : ℕ} : ((Fin k → ℕ) →₀ ℝ) →ₗ[ℝ] (Fin k → ℕ) →₀ ℝ where
  toFun l := Finsupp.onFinset (Fintype.piFinset fun i ↦ range (l.support.sup (· i) + 1))
    (fun r ↦ (∏ i, μ (r i) * φ (r i)) * l.sum fun d ld ↦
      if ∀ i, r i ∣ d i ∧ Squarefree (d i) then ld / ∏ i, d i else 0) fun r hr ↦ by
      simp_rw [Fintype.mem_piFinset, mem_range_succ_iff]
      rw [mul_ne_zero_iff] at hr
      obtain ⟨d, hld, hd⟩ := exists_ne_zero_of_sum_ne_zero hr.2
      simp only [ne_eq, ite_eq_right_iff, div_eq_zero_iff, Finset.prod_eq_zero_iff,
        cast_eq_zero, Classical.not_imp] at hd
      exact fun i ↦ (le_of_dvd (by grind) (hd.1 i).1).trans <| le_sup (f := (· i)) hld
  map_add' l₁ l₂ := ext fun r ↦ by
    simp_rw [Finsupp.add_apply, Finsupp.onFinset_apply]
    rw [sum_add_index (by simp) (by simp [add_div, ite_add_zero]), mul_add]
  map_smul' c l := ext fun r ↦ by
    simp_rw [Finsupp.smul_apply, Finsupp.onFinset_apply]
    rw [sum_smul_index (by simp), RingHom.id_apply, smul_eq_mul]
    simp_rw [mul_div_assoc, ← mul_ite_zero, ← Finsupp.mul_sum]
    ac_rfl

/-- The linear map from the sieve coefficients `l` to their `m`-restricted transformed
coefficients. -/
@[pg_tag "bg246" "def_ym_vars"]
noncomputable def ym {k : ℕ} (m : Fin k) : ((Fin k → ℕ) →₀ ℝ) →ₗ[ℝ] (Fin k → ℕ) →₀ ℝ where
  toFun l := Finsupp.onFinset (Fintype.piFinset fun i ↦ range (l.support.sup (· i) + 1))
    (fun r ↦ (∏ i, μ (r i) * g (r i)) * l.sum fun d ld ↦
      if d m = 1 ∧ ∀ i, r i ∣ d i ∧ Squarefree (d i) then ld / ∏ i, φ (d i) else 0) fun r hr ↦ by
      simp_rw [Fintype.mem_piFinset, mem_range_succ_iff]
      rw [mul_ne_zero_iff] at hr
      obtain ⟨d, hld, hd⟩ := exists_ne_zero_of_sum_ne_zero hr.2
      simp only [ne_eq, ite_eq_right_iff, div_eq_zero_iff, Finset.prod_eq_zero_iff,
        cast_eq_zero, Classical.not_imp, Nat.totient_eq_zero] at hd
      exact fun i ↦ (le_of_dvd (by grind) (hd.1.2 i).1).trans <| le_sup (f := (· i)) hld
  map_add' l₁ l₂ := ext fun r ↦ by
    simp_rw [Finsupp.add_apply, Finsupp.onFinset_apply]
    rw [sum_add_index (by simp) (by simp [add_div, ite_add_zero]), mul_add]
  map_smul' c l := ext fun r ↦ by
    simp_rw [Finsupp.smul_apply, Finsupp.onFinset_apply]
    rw [sum_smul_index (by simp), RingHom.id_apply, smul_eq_mul]
    simp_rw [mul_div_assoc, ← mul_ite_zero, ← Finsupp.mul_sum]
    ac_rfl

/-- The inverse linear transform from transformed coefficients to sieve coefficients. -/
@[pg_tag "bg246" "def_lambda_from_y"]
noncomputable def yToL {k : ℕ} : ((Fin k → ℕ) →₀ ℝ) →ₗ[ℝ] (Fin k → ℕ) →₀ ℝ where
  toFun y := Finsupp.onFinset (Fintype.piFinset fun i ↦ range (y.support.sup (· i) + 1))
    (fun d ↦ (∏ i, μ (d i) * d i) * y.sum fun r yr ↦
      if ∀ i, d i ∣ r i ∧ Squarefree (r i) then yr / ∏ i, φ (r i) else 0) fun d hd ↦ by
      simp_rw [Fintype.mem_piFinset, mem_range_succ_iff]
      rw [mul_ne_zero_iff] at hd
      obtain ⟨r, hyr, hr⟩ := exists_ne_zero_of_sum_ne_zero hd.2
      simp only [ne_eq, ite_eq_right_iff, div_eq_zero_iff, Finset.prod_eq_zero_iff,
        cast_eq_zero, Classical.not_imp, Nat.totient_eq_zero] at hr
      exact fun i ↦ (le_of_dvd (by grind) (hr.1 i).1).trans <| le_sup (f := (· i)) hyr
  map_add' l₁ l₂ := ext fun r ↦ by
    simp_rw [Finsupp.add_apply, Finsupp.onFinset_apply]
    rw [sum_add_index (by simp) (by simp [add_div, ite_add_zero]), mul_add]
  map_smul' c l := ext fun r ↦ by
    simp_rw [Finsupp.smul_apply, Finsupp.onFinset_apply]
    rw [sum_smul_index (by simp), RingHom.id_apply, smul_eq_mul]
    simp_rw [mul_div_assoc, ← mul_ite_zero, ← Finsupp.mul_sum]
    ac_rfl

@[pg_tag "bg246" "def_y_from_lambda", pg_tag "bg246" "def_y_vars"]
theorem lToY_apply' : lToY l r = (∏ i, μ (r i) * φ (r i)) * l.sum fun d ld ↦
    if ∀ i, r i ∣ d i ∧ Squarefree (d i) then ld / ∏ i, d i else 0 := rfl

@[pg_tag "bg246" "def_y_from_lambda", pg_tag "bg246" "def_y_vars"]
theorem lToY_apply (hl : l.HasPermissibleSupport R W) :
    lToY l r = (∏ i, μ (r i) * φ (r i)) * l.sum fun d ld ↦
      if ∀ i, r i ∣ d i then ld / ∏ i, d i else 0 := by
  rw [lToY_apply']
  congr 1
  exact sum_congr rfl fun d hd ↦ by simp [hl.squarefree_of_ne_zero (mem_support_iff.mp hd)]

@[pg_tag "bg246" "lem_y_permissible_support"]
theorem _root_.Finsupp.HasPermissibleSupport.lToY (hl : l.HasPermissibleSupport R W) :
    (lToY l).HasPermissibleSupport R W := fun r hyr ↦ by
  simp_rw [mem_support_iff, lToY_apply hl, mul_ne_zero_iff] at hyr
  obtain ⟨d, hld, hd⟩ := exists_ne_zero_of_sum_ne_zero hyr.2
  simp_rw [ite_ne_right_iff, div_ne_zero_iff] at hd
  exact mem_permissibleSupport_of_dvd (hl hld) hd.1

@[pg_tag "bg246" "def_lambda_from_y"]
theorem yToL_apply' : yToL y d = (∏ i, μ (d i) * d i) * y.sum fun r yr ↦
    if ∀ i, d i ∣ r i ∧ Squarefree (r i) then yr / ∏ i, φ (r i) else 0 := rfl

@[pg_tag "bg246" "def_lambda_from_y"]
theorem yToL_apply (hy : y.HasPermissibleSupport R W) :
    yToL y d = (∏ i, μ (d i) * d i) * y.sum fun r yr ↦
      if ∀ i, d i ∣ r i then yr / ∏ i, φ (r i) else 0 := by
  rw [yToL_apply']
  congr 1
  exact sum_congr rfl fun r hr ↦ by simp [hy.squarefree_of_ne_zero (mem_support_iff.mp hr)]

@[pg_tag "bg246" "lem_lambda_y_permissible_support"]
theorem _root_.Finsupp.HasPermissibleSupport.yToL (hy : y.HasPermissibleSupport R W) :
    (yToL y).HasPermissibleSupport R W := fun d hd ↦ by
  simp_rw [mem_support_iff, yToL_apply hy, mul_ne_zero_iff] at hd
  obtain ⟨r, hyr, hr⟩ := exists_ne_zero_of_sum_ne_zero hd.2
  simp_rw [ite_ne_right_iff, div_ne_zero_iff] at hr
  exact mem_permissibleSupport_of_dvd (hy hyr) hr.1

@[pg_tag "bg246" "def_ym_vars"]
theorem ym_apply' : ym m l r = (∏ i, μ (r i) * g (r i)) * l.sum fun d ld ↦
    if d m = 1 ∧ ∀ i, r i ∣ d i ∧ Squarefree (d i) then ld / ∏ i, φ (d i) else 0 := rfl

@[pg_tag "bg246" "def_ym_vars"]
theorem ym_apply (hl : l.HasPermissibleSupport R W) :
    ym m l r = (∏ i, μ (r i) * g (r i)) * l.sum fun d ld ↦
      if d m = 1 ∧ ∀ i, r i ∣ d i then ld / ∏ i, φ (d i) else 0 := by
  rw [ym_apply']
  congr 1
  exact sum_congr rfl fun d hd ↦ by simp [hl.squarefree_of_ne_zero (mem_support_iff.mp hd)]

theorem squarefree_of_lToY_ne_zero (h : lToY l r ≠ 0) (i : Fin k) : Squarefree (r i) := by
  rw [lToY_apply', mul_ne_zero_iff] at h
  obtain ⟨d, hld, hd⟩ := exists_ne_zero_of_sum_ne_zero h.2
  rw [ite_ne_right_iff] at hd
  exact (hd.1 i).2.squarefree_of_dvd (hd.1 i).1

theorem squarefree_of_yToL_ne_zero (h : yToL y d ≠ 0) (i : Fin k) : Squarefree (d i) := by
  rw [yToL_apply', mul_ne_zero_iff] at h
  obtain ⟨r, hyr, hr⟩ := exists_ne_zero_of_sum_ne_zero h.2
  rw [ite_ne_right_iff] at hr
  exact (hr.1 i).2.squarefree_of_dvd (hr.1 i).1

theorem lToY_single : lToY (single d c) r = (∏ i, μ (r i) * φ (r i)) *
    if ∀ i, r i ∣ d i ∧ Squarefree (d i) then c / ∏ i, d i else 0 := by
  rw [lToY_apply', sum_single_index (by simp)]

theorem yToL_single : yToL (single r c) d = (∏ i, μ (d i) * d i) *
    if ∀ i, d i ∣ r i ∧ Squarefree (r i) then c / ∏ i, φ (r i) else 0 := by
  rw [yToL_apply', sum_single_index (by simp)]

theorem support_lToY_single_subset :
    (lToY (single d c)).support ⊆ Fintype.piFinset fun i ↦ (d i).divisors := fun r hr ↦ by
  rw [mem_support_iff, lToY_single, mul_ne_zero_iff, ite_ne_right_iff, div_ne_zero_iff,
    Nat.cast_ne_zero, Finset.prod_ne_zero_iff] at hr
  grind

theorem support_yToL_single_subset :
    (yToL (single r c)).support ⊆ Fintype.piFinset fun i ↦ (r i).divisors := fun r hr ↦ by
  rw [mem_support_iff, yToL_single, mul_ne_zero_iff, ite_ne_right_iff, div_ne_zero_iff,
    Nat.cast_ne_zero, Finset.prod_ne_zero_iff] at hr
  grind [totient_eq_zero]

@[pg_tag "bg246" "lem_lambda_from_y"]
theorem yToL_lToY : yToL (lToY l) d = if ∀ i, Squarefree (d i) then l d else 0 := by
  split_ifs with hd
  swap
  · exact by_contra fun H ↦ hd <| squarefree_of_yToL_ne_zero H
  induction l using Finsupp.induction with
  | zero => simp
  | single_add d₀ c _ _ _ ih =>
  simp only [map_add, Finsupp.add_apply, ih, add_left_inj]
  clear * - hd
  rw [yToL_apply', sum_of_support_subset _ support_lToY_single_subset _ (by simp)]
  simp_rw [lToY_single, mul_ite_zero, ite_div, zero_div, ← ite_and, ← sum_filter]
  by_cases! hd₀ : ¬∀ i, Squarefree (d₀ i) ∧ d i ∣ d₀ i
  · rw [sum_eq_zero fun r hr ↦ ?_, mul_zero, single_eq_of_ne (by aesop)]
    rw [mem_filter, Fintype.mem_piFinset] at hr
    grind [dvd_trans]
  rw [show Finset.filter _ _ = Fintype.piFinset fun i ↦ (d i).divisorsBetween (d₀ i) from
    Finset.ext fun r ↦ by
      simp only [mem_filter, Fintype.mem_piFinset, mem_divisors, ne_eq, mem_divisorsBetween_iff]
      grind [Squarefree.squarefree_of_dvd]]
  simp_rw [mul_div_left_comm, mul_div_assoc, ← Finset.mul_sum, Nat.cast_prod, Int.cast_prod,
    ← prod_div_distrib, div_div, Int.cast_mul, Int.cast_natCast]
  rw [← Finset.prod_univ_sum (fun i ↦ (d i).divisorsBetween _)
    (fun i ri ↦ ((μ ri * φ ri) / (d₀ i * φ ri) : ℝ)), ← mul_assoc]
  trans ?_ * ∏ i, ∑ j ∈ (d i).divisorsBetween (d₀ i), (μ j / d₀ i : ℝ)
  · refine congrArg₂ _ (by rfl) <| prod_congr rfl fun i _ ↦ sum_congr rfl fun j hj ↦ ?_
    simp only [mem_divisorsBetween_iff, ne_eq] at hj
    exact mul_div_mul_right _ _ <| by simpa using ne_zero_of_dvd_ne_zero hj.1 hj.2.2
  simp_rw [← sum_div, sum_divisorsBetween_coe_moebius (hd₀ _).2 (hd₀ _).1, Int.cast_ite,
    Int.cast_zero, ite_div, zero_div, prod_ite_zero, mem_univ, true_imp_iff, ← funext_iff]
  obtain rfl | hdd₀ := eq_or_ne d d₀
  swap
  · simp [hdd₀]
  rw [if_pos rfl, prod_div_distrib, prod_mul_distrib]
  trans c * ∏ i, (μ (d i) ^ 2 : ℝ)
  · simp_rw [sq, prod_mul_distrib]
    have : ∏ i, (d i : ℝ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ by
      simpa using (hd i).ne_zero
    field_simp
  simp_rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree (hd _), Int.cast_one, prod_const_one]
  simp

@[pg_tag "bg246" "lem_y_from_lambda"]
theorem lToY_yToL : lToY (yToL y) r = if ∀ i, Squarefree (r i) then y r else 0 := by
  split_ifs with hr
  swap
  · exact by_contra fun H ↦ hr <| squarefree_of_lToY_ne_zero H
  induction y using Finsupp.induction with
  | zero => simp
  | single_add r₀ c _ _ _ ih =>
  simp only [map_add, Finsupp.add_apply, ih, add_left_inj]
  clear * - hr
  rw [lToY_apply', sum_of_support_subset _ support_yToL_single_subset _ (by simp)]
  simp_rw [yToL_single, mul_ite_zero, ite_div, zero_div, ← ite_and, ← sum_filter]
  by_cases! hr₀ : ¬∀ i, Squarefree (r₀ i) ∧ r i ∣ r₀ i
  · rw [sum_eq_zero fun d hd ↦ ?_, mul_zero, single_eq_of_ne (by aesop)]
    rw [mem_filter, Fintype.mem_piFinset] at hd
    grind [dvd_trans]
  rw [show Finset.filter _ _ = Fintype.piFinset fun i ↦ (r i).divisorsBetween (r₀ i) from
    Finset.ext fun r ↦ by
      simp only [mem_filter, Fintype.mem_piFinset, mem_divisors, ne_eq, mem_divisorsBetween_iff]
      grind [Squarefree.squarefree_of_dvd]]
  simp_rw [mul_div_left_comm, mul_div_assoc, ← Finset.mul_sum, Nat.cast_prod, Int.cast_prod,
    ← prod_div_distrib, div_div, Int.cast_mul, Int.cast_natCast]
  rw [← Finset.prod_univ_sum (fun i ↦ (r i).divisorsBetween _)
    (fun i di ↦ ((μ di * di) / (φ (r₀ i) * di) : ℝ)), ← mul_assoc]
  trans ?_ * ∏ i, ∑ j ∈ (r i).divisorsBetween (r₀ i), (μ j / φ (r₀ i) : ℝ)
  · refine congrArg₂ _ (by rfl) <| prod_congr rfl fun i _ ↦ sum_congr rfl fun j hj ↦ ?_
    simp only [mem_divisorsBetween_iff, ne_eq] at hj
    exact mul_div_mul_right _ _ <| by simpa using ne_zero_of_dvd_ne_zero hj.1 hj.2.2
  simp_rw [← sum_div, sum_divisorsBetween_coe_moebius (hr₀ _).2 (hr₀ _).1, Int.cast_ite,
    Int.cast_zero, ite_div, zero_div, prod_ite_zero, mem_univ, true_imp_iff, ← funext_iff]
  obtain rfl | hrr₀ := eq_or_ne r r₀
  swap
  · simp [hrr₀]
  rw [if_pos rfl, prod_div_distrib, prod_mul_distrib]
  trans c * ∏ i, (μ (r i) ^ 2 : ℝ)
  · simp_rw [sq, prod_mul_distrib]
    have : ∏ i, (φ (r i) : ℝ) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ ↦ by
      simpa using (hr i).ne_zero
    field_simp
  simp_rw [← Int.cast_pow, moebius_sq_eq_one_of_squarefree (hr _), Int.cast_one, prod_const_one]
  simp

@[pg_tag "bg246" "lem_ym_support"]
theorem eq_one_of_ym_ne_zero (hym : ym m l r ≠ 0) : r m = 1 := by
  rw [ym_apply', mul_ne_zero_iff] at hym
  obtain ⟨d, hld, hd⟩ := exists_ne_zero_of_sum_ne_zero hym.2
  grind [dvd_one]

end PrimeGaps
