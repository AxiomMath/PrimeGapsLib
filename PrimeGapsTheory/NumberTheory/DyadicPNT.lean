/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.PNT
public import PrimeGapsTheory.NumberTheory.PrimeCountingInterval

import PrimeGapsTheory.Tactic.PaperTag

/-! # Prime Number Theorem on a Dyadic Interval

The bulk of prime number theorem is Alex Kontorovich's library `PrimeNumberTheoremAnd`.
-/

@[expose] public section

open PrimeGaps Real Filter Asymptotics
open scoped Chebyshev

namespace PNT

private lemma dyadic_main_term {N : ℕ} (hN : 2 ≤ N) :
    |(2 * N : ℝ) / log (2 * N) - 2 * N / log N| ≤ 2 * log 2 * N / log N ^ 2 := by
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogNpos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN)
  have hlogmul : log (2 * N : ℝ) = log 2 + log N := log_mul (by positivity) hNpos.ne'
  rw [hlogmul]
  have hlog2pos : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have heq : (2 * N : ℝ) / (log 2 + log N) - 2 * N / log N =
      -(2 * N * log 2 / ((log 2 + log N) * log N)) := by grind
  rw [heq, abs_neg, abs_of_pos (div_pos (mul_pos (by positivity) hlog2pos)
    (mul_pos (by positivity) hlogNpos))]
  have hden : log (N : ℝ) ^ 2 ≤ (log 2 + log N) * log N := by nlinarith
  calc 2 * N * log 2 / ((log 2 + log N) * log N)
      ≤ 2 * N * log 2 / log N ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hlogNpos) hden
    _ = 2 * log 2 * N / log N ^ 2 := by ring

/-- `π(N) = N/log N + O(N/(log N)^2) as N → ∞`. -/
@[pg_tag "bg246" "thm_PNT_XN"]
theorem primeCountingIoc_self_two_mul : ∃ (C : ℝ) (N₀ : ℕ), ∀ N ≥ N₀,
      |Nat.primeCountingIoc N (2 * N) - N / Real.log N| ≤ C * N / Real.log N ^ 2 := by
  obtain ⟨C, N₀, hC⟩ := primeCounting
  refine ⟨3 * |C| + 2 * log 2, max N₀ 2, fun N hN ↦ ?_⟩
  have hN₀ : N₀ ≤ N := le_trans (le_max_left ..) hN
  have hN2 : 2 ≤ N := le_trans (le_max_right ..) hN
  have hNpos : (0 : ℝ) < N := by positivity
  have hlogNpos : 0 < log (N : ℝ) := log_pos (by exact_mod_cast hN2)
  have hlogmono : log (N : ℝ) ≤ log (2 * N : ℝ) := log_le_log hNpos (by nlinarith)
  have habs : C ≤ |C| := le_abs_self C
  have hCN' : |(N.primeCounting : ℝ) - N / log N| ≤ |C| * N / log N ^ 2 :=
    (hC N hN₀).trans (by gcongr)
  have hC2N := hC (2 * N) (hN₀.trans (by omega))
  push_cast at hC2N
  have hC2N' : |((2 * N).primeCounting : ℝ) - (2 * N) / log (2 * N)| ≤ 2 * |C| * N / log N ^ 2 :=
    hC2N.trans <| calc
      C * (2 * N : ℝ) / log (2 * N : ℝ) ^ 2 ≤ |C| * (2 * N : ℝ) / log (N : ℝ) ^ 2 := by gcongr
      _ = 2 * |C| * N / log N ^ 2 := by ring
  have hmain := dyadic_main_term hN2
  rw [Nat.cast_primeCountingIoc (by omega : N ≤ 2 * N)]
  grind

end PNT
