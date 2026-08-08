/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.PermissibleSupport.Basic
public import PrimeGapsTheory.Sieve.Sums
public import PrimeGapsTheory.Foundations.SieveDatum

import PrimeGapsTheory.Tactic.PaperTag

/-!
# From positive sieve sums to small prime gaps

Combinatorial deductions from positivity of a sieve sum to bounded consecutive prime gaps.

## Main definitions

* `ContainsAtLeastPrimes`: The assertion that an interval contains a prescribed number of primes.

## Main results

* `lem_S_positive_implies_primes`: A positive weighted prime-count sum has a summand whose
  prime count meets the target.
* `maynardTao_endgame`: Positivity of the combined sieve sum yields infinitely many prime-rich
  translates.
* `frequently_prime_gap_le_of_frequently_interval`: Frequent prime-rich intervals yield frequent
  bounded prime gaps.
-/

@[expose] public section

open scoped Finset
open scoped BigOperators

namespace PrimeGaps

/-- If `S = ∑ (∑ χ_P(n+h_i) - ρ) · w_n > 0` with `w_n ≥ 0`, then some `n`
has at least `⌊ρ+1⌋` primes among `n + h_1, …, n + h_k`. -/
@[pg_tag "bg246" "lem_S_positive_implies_primes"]
theorem lem_S_positive_implies_primes (N k : ℕ) (h : Fin k → ℕ) (ρ : ℝ) (hρ : 0 < ρ)
    (weight : ℕ → ℝ) (hw : ∀ n ∈ Finset.Ioc N (2 * N), 0 ≤ weight n)
    (hS_pos : 0 < ∑ n ∈ Finset.Ioc N (2 * N), (#(Finset.univ.filter
          (fun i : Fin k ↦ Nat.Prime (n + h i))) - ρ) * weight n) :
    ∃ n ∈ Finset.Ioc N (2 * N), ⌊ρ + 1⌋₊ ≤
        #(Finset.univ.filter (fun i : Fin k ↦ Nat.Prime (n + h i))) := by
  by_contra! hcon
  refine absurd hS_pos (not_lt.mpr <| Finset.sum_nonpos fun n hn ↦ ?_)
  set m := #(Finset.univ.filter (fun i : Fin k ↦ Nat.Prime (n + h i)))
  have h1 : (m : ℝ) + 1 ≤ (⌊ρ + 1⌋₊ : ℝ) := by exact_mod_cast hcon n hn
  refine mul_nonpos_of_nonpos_of_nonneg ?_ (hw n hn)
  linarith [Nat.floor_le (show (0 : ℝ) ≤ ρ + 1 by linarith)]

end PrimeGaps

namespace PrimeGaps

open Filter Finset

variable {k : ℕ}

open scoped PrimeGaps.sieveModulus in
/-- **Positivity of the combined sum forces a good `n` in the sieve window.** If
`0 < S₂ h l N w₀ − ρ · S₁ h l N w₀`, then some `n` in the sum's index set (i.e. `N < n ≤ 2N`
with `(n : ZMod (W N)) = w₀`) has strictly more than `ρ` primes among `n + h₁,
  …, n + h_k`.
-/
theorem exists_prime_count_gt_of_S_pos (h : Fin k → ℕ) (l : (Fin k → ℕ) → ℝ)
    (ρ : ℝ) (N : ℕ) (w₀ : ZMod (W N))
    (hS : 0 < S₂ h l N w₀ - ρ * S₁ h l N w₀) :
    ∃ n ∈ (Ioc N (2 * N)).filter (fun n : ℕ ↦ (n : ZMod (W N)) = w₀),
      ρ < (#{i : Fin k | (n + h i).Prime} : ℝ) := by
  by_contra! hcon
  have hle : S₂ h l N w₀ ≤ ρ * S₁ h l N w₀ := by
    unfold S₂ S₁
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun n hn ↦ mul_le_mul_of_nonneg_right (hcon n hn) w_nonneg
  linarith

/-- `⌊ρ + 1⌋ ≤ m` for a real `ρ < m`. -/
theorem floor_add_one_le_of_lt_natCast {ρ : ℝ} {m : ℕ} (hρ : ρ < m) : ⌊ρ + 1⌋ ≤ (m : ℤ) := by
  rw [Int.floor_add_one]
  exact Int.floor_lt.mpr (by exact_mod_cast hρ)

open scoped PrimeGaps.sieveModulus in
/-- **Maynard–Tao endgame.** Fix an admissible tuple `h : Fin k → ℕ`, a target constant `ρ`,
and compatible residues `v₀ N ∈ ZMod (W N)`. If for every sufficiently
large `N` there is a weight `l : (Fin k → ℕ) →₀ ℝ` such that
`S₂ h l N (v₀ N) − ρ · S₁ h l N (v₀ N) > 0`, then there are infinitely many
`n : ℕ` for which at least `⌊ρ + 1⌋` of `n + h₁, …, n + h_k` are prime. -/
@[pg_tag "bg246" "lem_infinitely_many"]
theorem maynardTao_endgame (h : Fin k → ℕ) (ρ : ℝ) (v₀ : ∀ N, ZMod (W N))
    (hpos : ∀ᶠ N in atTop, ∃ l : (Fin k → ℕ) →₀ ℝ, 0 < S₂ h l N (v₀ N) - ρ * S₁ h l N (v₀ N)) :
    {n : ℕ | ⌊ρ + 1⌋ ≤ (#{i : Fin k | (n + h i).Prime} : ℤ)}.Infinite := by
  refine Set.infinite_of_not_bddAbove (not_bddAbove_iff.mpr fun M ↦ ?_)
  obtain ⟨N, ⟨l, hS⟩, hNM⟩ := (hpos.and (eventually_ge_atTop M)).exists
  obtain ⟨n, hn_mem, hn_gt⟩ := exists_prime_count_gt_of_S_pos h l ρ N (v₀ N) hS
  rw [mem_filter, mem_Ioc] at hn_mem
  exact ⟨n, floor_add_one_le_of_lt_natCast hn_gt, hNM.trans_lt hn_mem.1.1⟩

end PrimeGaps

open Filter

namespace PrimeGaps

/-- The closed interval `[n, n + L]` contains at least `r` distinct primes. -/
def ContainsAtLeastPrimes (n L r : ℕ) : Prop := r ≤ #((Finset.Icc n (n + L)).filter Nat.Prime)

end PrimeGaps

namespace Nat

/-- `Nat.count Nat.Prime` tends to infinity: for every bound `M` there is `n`
with `M ≤ Nat.count Nat.Prime n`. -/
theorem count_prime_unbounded (M : ℕ) : ∃ n, M ≤ Nat.count Nat.Prime n :=
  ⟨Nat.nth Nat.Prime M + 1, le_trans (Nat.le_succ M)
    (Nat.count_nth_succ_of_infinite Nat.infinite_setOfPred_prime M).ge⟩

/-- The number of primes in `[n, n + L]` is the difference of Mathlib's
prime-counting function at `n + L + 1` and at `n`. -/
theorem primeCount_eq_count_sub (n L : ℕ) : #((Finset.Icc n (n + L)).filter Nat.Prime) =
      Nat.count Nat.Prime (n + L + 1) - Nat.count Nat.Prime n := by
  have hkey : Nat.count Nat.Prime (n + L + 1) =
      Nat.count Nat.Prime n + #((Finset.Icc n (n + L)).filter Nat.Prime) := by
    simp only [Nat.count_eq_card_filter_range]
    have hIcc : Finset.Icc n (n + L) = Finset.Ico n (n + L + 1) := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
    have hunion : Finset.range (n + L + 1) = Finset.range n ∪ Finset.Icc n (n + L) := by
      rw [hIcc, Finset.range_eq_Ico, Finset.range_eq_Ico,
        Finset.Ico_union_Ico_eq_Ico (Nat.zero_le n) (by omega : n ≤ n + L + 1)]
    have hdisj : Disjoint (Finset.range n) (Finset.Icc n (n + L)) := by
      simp only [Finset.disjoint_left, Finset.mem_range, Finset.mem_Icc]
      omega
    rw [hunion, Finset.filter_union,
        Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj)]
  omega

/-- `n ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime n)` — the `(count n)`-th prime
sits at or above `n`. -/
theorem le_prime_count (n : ℕ) : n ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime n) :=
  (Nat.count_le_iff_le_nth Nat.infinite_setOfPred_prime).mp le_rfl

end Nat

namespace PrimeGaps

/-- Upper bound on the `(m + r - 1)`-th prime when `[n, n + L]` has ≥ r primes,
with `m := Nat.count Nat.Prime n`. -/
theorem prime_upper_of_containsAtLeast
    {n L r : ℕ} (hr : 1 ≤ r) (hn : ContainsAtLeastPrimes n L r) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime n + (r - 1)) ≤ n + L := by
  have hcount := Nat.primeCount_eq_count_sub n L
  have hmono : Nat.count Nat.Prime n ≤ Nat.count Nat.Prime (n + L + 1) :=
    Nat.count_monotone Nat.Prime (by omega)
  have hr' : r ≤ #((Finset.Icc n (n + L)).filter Nat.Prime) := hn
  have hlt : Nat.count Nat.Prime n + (r - 1) < Nat.count Nat.Prime (n + L + 1) := by omega
  exact Nat.le_of_lt_succ (Nat.nth_lt_of_lt_count hlt)

/-- Gap bound at `m := Nat.count Nat.Prime n`. -/
theorem gap_le_of_containsAtLeast
    {n L r : ℕ} (hr : 1 ≤ r) (hn : ContainsAtLeastPrimes n L r) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime n + (r - 1)) -
      Nat.nth Nat.Prime (Nat.count Nat.Prime n) ≤ L := by
  have h1 : n ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime n) := Nat.le_prime_count n
  have h2 : Nat.nth Nat.Prime (Nat.count Nat.Prime n + (r - 1)) ≤ n + L :=
    prime_upper_of_containsAtLeast hr hn
  omega

/-- **Many-primes-in-intervals implies small gaps.** If for arbitrarily large `n` the
interval `[n, n + L]` contains at least `r` primes, then there are *infinitely many* `m`
with `p_{m + r - 1} - p_m ≤ L`, under the 0-indexed prime enumeration `Nat.nth Nat.Prime`. -/
@[pg_tag "bg246" "lem_many_primes_implies_small_gaps"]
theorem frequently_prime_gap_le_of_frequently_interval (r L : ℕ) (hr : 1 ≤ r)
    (h : ∃ᶠ n in atTop, ContainsAtLeastPrimes n L r) :
    ∃ᶠ m in atTop, Nat.nth Nat.Prime (m + (r - 1)) - Nat.nth Nat.Prime m ≤ L := by
  refine Filter.frequently_atTop.mpr fun M ↦ ?_
  obtain ⟨n₀, hn₀⟩ := Nat.count_prime_unbounded M
  obtain ⟨n, hn_ge, hn_prop⟩ := Filter.frequently_atTop.1 h n₀
  exact ⟨Nat.count Nat.Prime n, hn₀.trans (Nat.count_monotone Nat.Prime hn_ge),
    gap_le_of_containsAtLeast hr hn_prop⟩

end PrimeGaps
