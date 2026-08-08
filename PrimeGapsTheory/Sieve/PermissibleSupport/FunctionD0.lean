/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PrimeGapsTheory.Tactic.PaperTag

/-! # The `W`-trick threshold `D₀`

The triple logarithm `D₀ N = log (log (log N))`, which cuts off the primes entering the sieve
modulus `W`, together with its monotonicity and growth properties.

## Main definitions

* `PrimeGaps.D₀`: the threshold `D₀ N = log (log (log N))`.
-/

@[expose] public section

open Real

namespace PrimeGaps

/-- `D₀ N = log (log (log N))`, the triple-logarithm `W`-trick threshold. -/
@[pg_tag "bg246" "def_D_0"]
noncomputable def D₀ (N : ℝ) : ℝ := log (log (log N))

lemma D₀_le_self {N : ℝ} (hN : rexp 1 ≤ N) : D₀ N ≤ N := by
  unfold D₀
  have h : 1 ≤ log N := by grw [← log_exp 1, hN]
  grind [log_le_self, log_nonneg, exp_nonneg]

lemma D₀_le_self_iff {N M : ℝ} (hN : rexp 1 < N) : D₀ N ≤ M ↔ N ≤ rexp (rexp (rexp M)) := by
  unfold D₀
  have h : 1 < log N := by
    rw [← log_exp 1]
    exact log_lt_log (exp_pos 1) hN
  grind [log_le_iff_le_exp, log_pos, exp_pos]

/-- Past the triple exponential threshold `rexp (rexp (rexp M)) + 1`, the triple logarithm `D₀`
exceeds `M`. -/
lemma lt_D₀_of_le {M x : ℝ} (hx : rexp (rexp (rexp M)) + 1 ≤ x) : M < D₀ x := by
  have hxe : rexp 1 < x := (exp_le_exp.mpr (one_le_exp (exp_pos M).le)).trans_lt (by linarith)
  by_contra hle
  linarith [(D₀_le_self_iff hxe).mp (not_lt.mp hle)]

attribute [local grind .] log_pos Set.MapsTo log_exp in
attribute [local grind =_] exp_zero in
lemma D₀_strictMonoOn : StrictMonoOn D₀ (Set.Ioi (rexp 1)) := by
  change StrictMonoOn (log ∘ log ∘ log) (Set.Ioi (rexp 1))
  refine strictMonoOn_log.comp (strictMonoOn_log.comp (strictMonoOn_log.mono ?_) ?_) ?_
  · simpa using exp_nonneg _
  · grind [exp_lt_exp.2 zero_lt_one]
  · grind [log_lt_log (exp_pos 1)]

lemma _root_.Real.log_even : Function.Even log := log_neg_eq_log

lemma D₀_even : Function.Even D₀ := by
  change Function.Even (log ∘ log ∘ log)
  exact (log_even.left_comp _).left_comp _

end PrimeGaps
