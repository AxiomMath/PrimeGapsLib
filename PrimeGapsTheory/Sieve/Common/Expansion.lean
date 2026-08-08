/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Data.Nat.GCD.Basic

/-!
# Expanding a squared divisor sum and swapping the summations

Every sieve moment in this development begins by expanding the square of an inner divisor sum
and swapping the order of summation:

`∑ₙ f(n) · (∑_{d ∈ D, d ∣ n} λ d)² = ∑_d ∑_e λ d · λ e · ∑_{n : lcm(d,e) ∣ n} f(n)`.

The only arithmetic input is that simultaneous divisibility by `d` and by `e` is the same as
divisibility by their coordinatewise least common multiple. That is taken here as a hypothesis
`hQ` on an abstract divisibility predicate `Q`, so the identity applies verbatim to the first
moment (index set `(⌊N⌋, ⌊2N⌋] ⊆ ℤ`, weight `1`) and to the second moment (index set
`(N, 2N] ⊆ ℕ`, weight the prime indicator of `n + hₘ`).

## Main results

* `PrimeGaps.Expansion.mul_sq_sum_filter`: the pointwise square expansion.
* `PrimeGaps.Expansion.sum_ite_mul_sq`: the expansion summed over a gated index set.
-/

@[expose] public section

namespace PrimeGaps.Expansion

/-- Expanding the square of a filtered divisor sum: if simultaneous `q`-divisibility by `d` and
by `e` is the same as `q`-divisibility by their coordinatewise least common multiple, then
`w · (∑_{d ∈ D, q d} λ d)² = ∑_d ∑_e [q (lcm d e)] · λ d · λ e · w`. -/
lemma mul_sq_sum_filter {k : ℕ} (q : (Fin k → ℕ) → Prop) [DecidablePred q]
    (hq : ∀ d e : Fin k → ℕ, (q d ∧ q e) ↔ q fun i ↦ Nat.lcm (d i) (e i))
    (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ) (w : ℝ) :
    w * (∑ d ∈ D.filter q, lam d) ^ 2 =
      ∑ d ∈ D, ∑ e ∈ D, if q fun i ↦ Nat.lcm (d i) (e i) then lam d * lam e * w else 0 := by
  rw [Finset.sum_filter, sq, Finset.sum_mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  by_cases hde : q fun i ↦ Nat.lcm (d i) (e i)
  · obtain ⟨hd, he⟩ := (hq d e).mpr hde
    rw [if_pos hde, if_pos hd, if_pos he]; ring
  · rw [if_neg hde]
    rcases not_and_or.mp (fun hh ↦ hde ((hq d e).mp hh)) with hd | he
    · rw [if_neg hd]; ring
    · rw [if_neg he]; ring

/-- The square expansion of `PrimeGaps.Expansion.mul_sq_sum_filter`, summed over an index set `T`
gated by a predicate `P` and weighted by `w`, with the summations swapped:

`∑_{n ∈ T} [P n] · w n · (∑_{d ∈ D, Q n d} λ d)²
  = ∑_d ∑_e λ d · λ e · ∑_{n ∈ T} [P n ∧ Q n (lcm d e)] · w n`. -/
lemma sum_ite_mul_sq {ι : Type*} {k : ℕ} (T : Finset ι) (P : ι → Prop) [DecidablePred P]
    (w : ι → ℝ) (Q : ι → (Fin k → ℕ) → Prop) [∀ n, DecidablePred (Q n)]
    (hQ : ∀ (n : ι) (d e : Fin k → ℕ), (Q n d ∧ Q n e) ↔ Q n fun i ↦ Nat.lcm (d i) (e i))
    (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ) :
    (∑ n ∈ T, if P n then w n * (∑ d ∈ D.filter (Q n), lam d) ^ 2 else 0) =
      ∑ d ∈ D, ∑ e ∈ D, lam d * lam e *
        ∑ n ∈ T, if P n ∧ Q n fun i ↦ Nat.lcm (d i) (e i) then w n else 0 := by
  have key : ∀ n ∈ T, (if P n then w n * (∑ d ∈ D.filter (Q n), lam d) ^ 2 else 0) =
      ∑ d ∈ D, ∑ e ∈ D,
        if P n ∧ Q n fun i ↦ Nat.lcm (d i) (e i) then lam d * lam e * w n else 0 := by
    intro n _
    by_cases hP : P n
    · rw [if_pos hP, mul_sq_sum_filter (Q n) (hQ n) D lam (w n)]
      exact Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ by
        simp only [hP, true_and]
    · rw [if_neg hP]
      exact (Finset.sum_eq_zero fun _ _ ↦ Finset.sum_eq_zero fun _ _ ↦ if_neg fun hh ↦ hP hh.1).symm
  rw [Finset.sum_congr rfl key, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ ↦ by split_ifs <;> ring

end PrimeGaps.Expansion

end
