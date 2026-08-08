/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.SpecialFunctions.Stirling
public import Mathlib.NumberTheory.Chebyshev

/-!
# Prime-sum estimates (shared Mertens machinery)

Canonical home for the elementary Mertens estimates that the sieve development
re-derives across many files. This module collects the **Mertens first-theorem
foundation** — the log-factorial identity, the ψ (Chebyshev) bound, and the
resulting `|∑_{d≤N} Λ(d)/d − log N| ≤ log 4 + 5` — proved once from Mathlib's von
Mangoldt / Chebyshev / Stirling API, so that `slem_gg_log_sum`, `lem_mertens_tau_k`,
and their descendants cite it instead of each carrying an independent derivation.
-/

@[expose] public section

open ArithmeticFunction Real
open scoped Nat

namespace PrimeGaps

/-- Log-factorial identity: `∑_{1 ≤ n ≤ N} log n = ∑_{1 ≤ d ≤ N} Λ(d) · ⌊N/d⌋`. -/
theorem sum_log_eq_sum_vonMangoldt_mul_div (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = ∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ) := by
  have h := sum_Ioc_mul_zeta_eq_sum vonMangoldt N
  aesop

/-- Key floating bound: `|∑_{d≤N} Λd·⌊N/d⌋ − N·T| ≤ ψ(N)` where `T = ∑_{d≤N} Λd/d`. -/
theorem abs_sum_vonMangoldt_div_sub (N : ℕ) :
    |(∑ d ∈ Finset.Ioc 0 N, Λ d * ((N / d : ℕ) : ℝ)) - (N : ℝ) * ∑ d ∈ Finset.Ioc 0 N, Λ d / d| ≤
      ∑ d ∈ Finset.Ioc 0 N, Λ d := by
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hbound : ∀ d ∈ Finset.Ioc 0 N, |Λ d * ((N / d : ℕ) : ℝ) - (N : ℝ) * (Λ d / d)| ≤ Λ d := by
    intro d hd
    obtain ⟨hd0, hdN⟩ := Finset.mem_Ioc.mp hd
    have hdpos : (0 : ℝ) < d := by positivity
    have hLnn : 0 ≤ Λ d := vonMangoldt_nonneg
    have hle : ((N / d : ℕ) : ℝ) ≤ (N : ℝ) / d := Nat.cast_div_le
    have hdm : (d : ℝ) * ((N / d : ℕ) : ℝ) + ((N % d : ℕ) : ℝ) = N := by
      exact_mod_cast congrArg (Nat.cast (R := ℝ)) (Nat.div_add_mod N d)
    have hmod : ((N % d : ℕ) : ℝ) < (d : ℝ) := by exact_mod_cast Nat.mod_lt N hd0
    have hlt : (N : ℝ) / d < ((N / d : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ hdpos]
      linarith
    have heq : (N : ℝ) * (Λ d / d) = Λ d * ((N : ℝ) / d) := by ring
    rw [heq, ← mul_sub, abs_mul, abs_of_nonneg hLnn]
    have habs : |((N / d : ℕ) : ℝ) - (N : ℝ) / d| ≤ 1 := by grind
    exact mul_le_of_le_one_right hLnn habs
  calc |∑ d ∈ Finset.Ioc 0 N, (Λ d * ((N / d : ℕ) : ℝ) - (N : ℝ) * (Λ d / d))|
      ≤ ∑ d ∈ Finset.Ioc 0 N, |Λ d * ((N / d : ℕ) : ℝ) - (N : ℝ) * (Λ d / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Ioc 0 N, Λ d := Finset.sum_le_sum hbound

/-- `∑_{n∈Ioc 0 N} Real.log n = Real.log (N !)`. -/
theorem sum_log_eq_log_factorial (N : ℕ) :
    ∑ n ∈ Finset.Ioc 0 N, Real.log n = Real.log (N ! : ℝ) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Ioc_succ_top (Nat.zero_le n), ih, Nat.factorial_succ, Nat.cast_mul,
      Real.log_mul (by positivity) (by positivity)]
    grind

/-- Bounds on `∑_{n∈Ioc 0 N} log n`: within `N` of `N log N`, for `N ≥ 1`. -/
theorem abs_sum_log_sub_le {N : ℕ} (hN : 1 ≤ N) :
    |(∑ n ∈ Finset.Ioc 0 N, Real.log n) - (N : ℝ) * Real.log N| ≤ (N : ℝ) := by
  have hNe : N ≠ 0 := by omega
  rw [sum_log_eq_log_factorial]
  have hup : Real.log (N ! : ℝ) ≤ (N : ℝ) * Real.log N := by
    rw [← sum_log_eq_log_factorial]
    calc ∑ n ∈ Finset.Ioc 0 N, Real.log n
        ≤ ∑ n ∈ Finset.Ioc 0 N, Real.log N :=
          Finset.sum_le_sum fun n hn ↦ Real.log_le_log (mod_cast (Finset.mem_Ioc.mp hn).1)
            (mod_cast (Finset.mem_Ioc.mp hn).2)
      _ = (N : ℝ) * Real.log N := by aesop
  have hlow := Stirling.le_log_factorial_stirling hNe
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have h2pi : 0 ≤ Real.log (2 * π) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  grind

/-- ψ-bound in the `Ioc 0 N` form: `∑_{d∈Ioc 0 N} Λ d ≤ (log 4 + 4)·N`. -/
theorem sum_vonMangoldt_Ioc_le (N : ℕ) :
    ∑ d ∈ Finset.Ioc 0 N, Λ d ≤ (Real.log 4 + 4) * (N : ℝ) := by
  have hpsi : Chebyshev.psi (N : ℝ) = ∑ n ∈ Finset.Icc 0 N, Λ n := by
    simp [Chebyshev.psi_eq_sum_Icc]
  have hIcc : ∑ n ∈ Finset.Icc 0 N, Λ n = ∑ d ∈ Finset.Ioc 0 N, Λ d := by
    rw [show Finset.Icc 0 N = insert 0 (Finset.Ioc 0 N) from ?_]
    · exact Finset.sum_insert_of_eq_zero_if_notMem fun _ ↦ ArithmeticFunction.map_zero
    · grind
  have hle := Chebyshev.psi_le_const_mul_self (x := (N : ℝ)) (by positivity)
  grind

/-- **Integer von-Mangoldt Mertens:** `|T_N − log N| ≤ log 4 + 5` where
`T_N = ∑_{d∈Ioc 0 N} Λd/d`, for `N ≥ 1`. -/
theorem abs_sum_vonMangoldt_div_sub_log {N : ℕ} (hN : 1 ≤ N) :
    |(∑ d ∈ Finset.Ioc 0 N, Λ d / d) - Real.log N| ≤ Real.log 4 + 5 := by
  have hNpos : (0 : ℝ) < N := by positivity
  set T := ∑ d ∈ Finset.Ioc 0 N, Λ d / d with hT
  have hid := sum_log_eq_sum_vonMangoldt_mul_div N
  have hfloat := abs_sum_vonMangoldt_div_sub N
  rw [← hT] at hfloat
  have hpsi := sum_vonMangoldt_Ioc_le N
  have hstir := abs_sum_log_sub_le hN
  have hcomb : |(N : ℝ) * T - (N : ℝ) * Real.log N| ≤ (Real.log 4 + 5) * (N : ℝ) := by grind
  rw [← mul_sub, abs_mul, abs_of_pos hNpos] at hcomb
  have hcomb' : (N : ℝ) * |T - Real.log N| ≤ (N : ℝ) * (Real.log 4 + 5) := by grind
  exact le_of_mul_le_mul_left hcomb' hNpos

end PrimeGaps
