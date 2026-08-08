/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.PSeries
public import Mathlib.NumberTheory.EulerProduct.Basic

/-!
# Shared Mertens estimates

Finite-sum and prime-power estimates used in Mertens-type arguments.

## Main results

* `finset_sum_le_exp_tsum_of_local`: A finite multiplicative sum is bounded by an
  exponential local sum.
* `tsum_ppow_eq_sum_range`: An infinite prime-power sum equals its finite nonzero range.
-/

@[expose] public section

open Real

open scoped BigOperators

namespace PrimeGaps

namespace MertensShared

/-- For a nonnegative multiplicative `f` whose local factors obey `∑ₖ f (p^k) ≤ exp (a p)`, every
finite sum satisfies `∑_{n ∈ u} f n ≤ exp (∑' n, a n)`. -/
lemma finset_sum_le_exp_tsum_of_local (f : ℕ → ℝ) (hf1 : f 1 = 1) (hf0 : f 0 = 0)
    (hf_nonneg : ∀ n, 0 ≤ f n)
    (hfmul : ∀ {a b : ℕ}, Nat.Coprime a b → f (a * b) = f a * f b)
    (hfsum : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ ↦ ‖f (p ^ k)‖))
    (a : ℕ → ℝ) (ha_nonneg : ∀ n, 0 ≤ a n) (ha_sum : Summable a)
    (hlocal : ∀ p : ℕ, p.Prime → (∑' k : ℕ, f (p ^ k)) ≤ rexp (a p))
    (u : Finset ℕ) :
    ∑ n ∈ u, f n ≤ rexp (∑' n : ℕ, a n) := by
  rw [← Finset.sum_erase u hf0]
  set K : ℕ := (u.sup _root_.id) + 1 with hK_def
  have hmem : ∀ n ∈ u.erase 0, n ∈ K.smoothNumbers := fun n hn ↦ by
    rw [Finset.mem_erase] at hn
    refine Nat.mem_smoothNumbers.mpr ⟨hn.1, fun q hq ↦ ?_⟩
    have hqle : q ≤ n :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn.1) (Nat.dvd_of_mem_primeFactorsList hq)
    have hnle : n ≤ u.sup _root_.id := Finset.le_sup (f := _root_.id) hn.2
    omega
  obtain ⟨_, Hhassum⟩ := EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      (f := f) hf1 (fun {a b} h ↦ hfmul h) (fun {p} hp ↦ hfsum hp) K
  rw [← Finset.sum_subtype_of_mem f hmem]
  refine (Summable.sum_le_tsum _ (fun i _ ↦ hf_nonneg _) Hhassum.summable).trans ?_
  rw [Hhassum.tsum_eq]
  refine (Finset.prod_le_prod (fun p _ ↦ tsum_nonneg fun k ↦ hf_nonneg _)
    (fun p hp ↦ hlocal p (Nat.prime_of_mem_primesBelow hp))).trans ?_
  rw [← Real.exp_sum]
  refine Real.exp_le_exp.mpr ?_
  refine (Finset.sum_le_sum_of_subset_of_nonneg
    (fun p hp ↦ Finset.mem_range.mpr (Nat.lt_of_mem_primesBelow hp))
    (fun n _ _ ↦ ha_nonneg n)).trans ?_
  exact Summable.sum_le_tsum _ (fun i _ ↦ ha_nonneg i) ha_sum

/-- **Finitely-supported local Euler factor.**  If `g (p ^ e)` vanishes for all
`e ≥ N`, then its local series collapses to the finite range sum
`∑_{e < N} g (p ^ e)`.  This is the common reduction step in the "local factor"
computations for functions supported on low prime-power exponents
(`gKernel_pp_tsum` with `N = 3`; `ASummand_local_factor` / `hAux_local_factor`
with `N = 2`). -/
lemma tsum_ppow_eq_sum_range (g : ℕ → ℝ) (p N : ℕ) (hvanish : ∀ e, N ≤ e → g (p ^ e) = 0) :
    (∑' e : ℕ, g (p ^ e)) = ∑ e ∈ Finset.range N, g (p ^ e) :=
  tsum_eq_sum fun e he ↦ hvanish e (by rwa [Finset.mem_range, not_lt] at he)

end MertensShared
end PrimeGaps
