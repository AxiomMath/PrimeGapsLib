/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.Estimates
public import PrimeGapsTheory.ArithmeticFunction.LYTransform.Basic
public import PrimeGapsTheory.Discrete.MaxRealAbs

import PrimeGapsTheory.Tactic.PaperTag

/-! # Estimates of arithmetic functions -/

@[expose] public section

open Real Finsupp Finset
open ArithmeticFunction

namespace PrimeGaps

@[pg_tag "bg246" "lem_lambda_max_bound"]
theorem max_yToL_le_const_mul_max_y_mul_log_pow {k R W : ℕ} {y : (Fin k → ℕ) →₀ ℝ}
    (hy : y.HasPermissibleSupport R W) (hR : 2 ≤ R) :
    (yToL y).maxRealAbs ≤ rexp (1 + 3 * k) * y.maxRealAbs * Real.log R ^ k := by
  refine maxRealAbs_le_iff.mpr fun d ↦ ?_
  simp only [yToL_apply hy, Int.cast_prod, Int.cast_mul, Int.cast_natCast, Nat.cast_prod,
    mem_filter, Nat.mem_finMulAntidiagLE_iff, ne_eq, zero_div, ite_self, implies_true,
    sum_of_support_subset _ <|
      hy.trans permissibleSupport_subset_filter_finMulAntidiagLE_squarefree,
    abs_mul, abs_prod, ← Int.cast_abs, Nat.abs_cast]
  classical grw [abs_moebius_le_one, abs_sum_le_sum_abs]
  simp only [Int.cast_one, one_mul, abs_ite, abs_div, abs_prod, Nat.abs_cast, abs_zero]
  grw [← sum_filter, y.le_maxRealAbs]
  simp_rw [← mul_one_div y.maxRealAbs, ← Finset.mul_sum, mul_left_comm _ y.maxRealAbs,
    filter_filter, ← Nat.cast_prod]
  have hynn := y.maxRealAbs_nonneg
  grw [prod_mul_sum_one_div_prod_totient_le hR, mul_left_comm, mul_assoc]

end PrimeGaps
