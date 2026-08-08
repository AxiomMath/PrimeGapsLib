/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.TdDecomposition.SizeHyp

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The A and B summands

The `ASummand`/`BSummand` series, their summability and partial-sum bounds.

## Main results

* `A_sub_partial_bound`
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius

open ArithmeticFunction

namespace PrimeGaps

/-- Summand of the Dirichlet sum `B`: for `M e : ℕ`,
`if e.Coprime M then μ(e) · log e / e^2 else 0`. -/
noncomputable def BSummand (M e : ℕ) : ℝ :=
  if e.Coprime M then (μ e : ℝ) * Real.log e / (e : ℝ) ^ 2 else 0

/-- The Dirichlet constant `B M = ∑'_{(e, M) = 1} μ(e) * log e / e ^ 2`. -/
@[pg_tag "bg246" "def_BM"]
noncomputable def B (M : ℕ) : ℝ := ∑' e : ℕ, BSummand M e

open scoped PrimeGaps.sieveModulus in
/-- `exp 1 ≤ W N` for all large `N`. -/
theorem W_eventually_ge_exp1 : ∀ᶠ N in Filter.atTop, rexp 1 ≤ (W N : ℝ) := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop (rexp 1),
    tendsto_natCast_atTop_atTop.eventually_gt_atTop (rexp (rexp (rexp 3)))]
    with N hN1 hN2
  have hD3 : (3 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by
    by_contra h
    push Not at h
    linarith [(PrimeGaps.D₀_le_self_iff hN1).mp h]
  have hWval : (3 : ℕ) ≤ W N := by
    rw [PrimeGaps.W_eq_primorial_D₀]
    exact (Nat.le_floor (by push_cast; linarith)).trans le_primorial_self
  calc rexp 1 ≤ 3 := by linarith [Real.exp_one_lt_d9]
    _ ≤ (W N : ℝ) := by exact_mod_cast hWval

/-- `ASummand M` is summable: dominated in absolute value by `1/e²`. -/
theorem summable_ASummand (M : ℕ) : Summable (ASummand M) := (A_summable M).of_abs

/-- `BSummand M` is summable: dominated in absolute value by `log e / e² = O(e^{-3/2})`. -/
theorem summable_BSummand (M : ℕ) : Summable (BSummand M) := by
  refine Summable.of_norm_bounded (g := fun e : ℕ ↦ 2 / (e : ℝ) ^ (3 / 2 : ℝ))
    ((((Real.summable_one_div_nat_rpow (p := 3 / 2)).mpr (by norm_num)).mul_left 2).congr
      fun e ↦ mul_one_div 2 _) fun e ↦ ?_
  rw [Real.norm_eq_abs, BSummand]
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp
  have hepos : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  have hrw : 2 * (e : ℝ) ^ (1 / 2 : ℝ) / (e : ℝ) ^ 2 = 2 / (e : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast (e : ℝ) 2, mul_div_assoc, ← Real.rpow_sub hepos,
      show (1 / 2 : ℝ) - ((2 : ℕ) : ℝ) = -(3 / 2) by norm_num, Real.rpow_neg hepos.le,
      ← div_eq_mul_inv]
  have hkey : Real.log e / (e : ℝ) ^ 2 ≤ 2 / (e : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← hrw]
    exact div_le_div_of_nonneg_right
      (by linarith [Real.log_natCast_le_rpow_div (ε := 1 / 2) e (by norm_num)]) (by positivity)
  split_ifs
  · exact (abs_moebius_mul_div_sq_le e (Real.log_nonneg (by exact_mod_cast he))).trans hkey
  · rw [abs_zero]; positivity

/-- Tail-truncation for `A`: for `m ≥ 1`, the partial sum of `ASummand M` over
`Icc 1 m` differs from `A M` by at most `1/m`.  (Because the tail `∑_{e>m} 1/e² ≤ 1/m`
and `|μe|/e² ≤ 1/e²`, and `ASummand M 0 = 0`.) -/
theorem A_sub_partial_bound (M : ℕ) (m : ℕ) (hm : 1 ≤ m) :
    |A M - ∑ e ∈ Finset.Icc 1 m, ASummand M e| ≤ 1 / m := by
  have hbound : ∀ e : ℕ, |ASummand M e| ≤ 1 / (e : ℝ) ^ 2 := fun e ↦ fM_apply M e ▸ abs_fM_le M e
  have hrange : ∑ e ∈ Finset.range (m + 1), ASummand M e = ∑ e ∈ Finset.Icc 1 m, ASummand M e := by
    rw [show Finset.range (m + 1) = insert 0 (Finset.Icc 1 m) by
        ext x; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega,
      Finset.sum_insert (by simp)]
    simp [ASummand]
  have htail : A M - ∑ e ∈ Finset.Icc 1 m, ASummand M e = ∑' i : ℕ, ASummand M (i + (m + 1)) := by
    rw [A, ← hrange, ← (summable_ASummand M).sum_add_tsum_nat_add (m + 1)]
    ring
  have hsummAbs := (summable_nat_add_iff (m + 1)).mpr (A_summable M)
  have hsummSq := (summable_nat_add_iff (m + 1)).mpr
    ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num))
  rw [htail]
  calc |∑' i : ℕ, ASummand M (i + (m + 1))| ≤ ∑' i : ℕ, |ASummand M (i + (m + 1))| :=
        norm_tsum_le_tsum_norm (f := fun i : ℕ ↦ ASummand M (i + (m + 1))) hsummAbs
    _ ≤ ∑' i : ℕ, 1 / ((i + (m + 1) : ℕ) : ℝ) ^ 2 :=
        Summable.tsum_le_tsum (fun i ↦ hbound _) hsummAbs hsummSq
    _ ≤ 1 / (m : ℝ) := by
        refine tsum_le_of_sum_le' (by positivity) fun u ↦ ?_
        have hsub : u.image (· + (m + 1)) ⊆ Finset.Ioc m (u.sup id + (m + 1)) := by
          intro e he
          simp only [Finset.mem_image] at he
          obtain ⟨i, hi, rfl⟩ := he
          have hi' : i ≤ u.sup id := Finset.le_sup (f := id) hi
          exact Finset.mem_Ioc.mpr ⟨by omega, by omega⟩
        have himg : ∑ e ∈ u.image (· + (m + 1)), 1 / (e : ℝ) ^ 2 =
            ∑ i ∈ u, 1 / ((i + (m + 1) : ℕ) : ℝ) ^ 2 :=
          Finset.sum_image fun x _ y _ h ↦ by omega
        calc ∑ i ∈ u, 1 / ((i + (m + 1) : ℕ) : ℝ) ^ 2
            = ∑ e ∈ u.image (· + (m + 1)), 1 / (e : ℝ) ^ 2 := himg.symm
          _ ≤ ∑ e ∈ Finset.Ioc m (u.sup id + (m + 1)), 1 / (e : ℝ) ^ 2 :=
              Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ ↦ by positivity
          _ ≤ 1 / (m : ℝ) := by
              simp only [one_div]
              linarith [sum_Ioc_inv_sq_le_sub (α := ℝ) (k := m) (n := u.sup id + (m + 1))
                  (by omega) (by omega),
                inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) (u.sup id + (m + 1)))]

end PrimeGaps
