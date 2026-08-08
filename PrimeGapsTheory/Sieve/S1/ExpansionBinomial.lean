/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.Expansion
public import PrimeGapsTheory.Sieve.Common.SumOverDivisors

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Binomial expansion of the first moment

Expands the square in the first sieve moment into a double divisor sum.

## Main results

* `lem_S1_expansion_S1_expansion`: Gives the double-sum expansion of the first moment.
-/

@[expose] public section

namespace PrimeGaps

open scoped BigOperators
open PrimeGaps.SumOverDivisors

/-- (arbitrary per-`n` weight `w`). The `S₁` and `S₂⁽ᵐ⁾` expansion lemmas are instantiations:
`w = 1` for `S₁`, `w n = χ_P(n + h m)` for `S₂⁽ᵐ⁾`.
-/
theorem lem_expansion_general (N W v_0 k : ℕ) (h : Fin k → ℕ) (w : ℕ → ℝ)
    (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N), if n % W = v_0 % W then
          w n * (∑ d ∈ D.filter (fun d ↦ ∀ i, d i ∣ n + h i), lam d) ^ 2
        else 0) =
    ∑ d ∈ D, ∑ e ∈ D, lam d * lam e * (∑ n ∈ Finset.Ioc N (2 * N),
          if n % W = v_0 % W ∧ ∀ i, Nat.lcm (d i) (e i) ∣ n + h i then w n else 0) :=
  PrimeGaps.Expansion.sum_ite_mul_sq (Finset.Ioc N (2 * N)) (fun n ↦ n % W = v_0 % W) w
    (fun n d ↦ ∀ i, d i ∣ n + h i) (fun n d e ↦ cond_lcm_iff h n d e) D lam

/-- S₁ expansion: `(∑_{d|n+h} λ_d)² = ∑_{d,e} λ_d λ_e · 1_{lcm(d,e)|n+h}`, summed over
`n ∈ (N, 2N] ∩ {n ≡ v_0 (W)}`.
-/
@[pg_tag "bg246" "lem_S1_expansion"]
theorem lem_S1_expansion_S1_expansion (N W v_0 : ℕ) (k : ℕ) (h : Fin k → ℕ) (D : Finset (Fin k → ℕ))
    (lam : (Fin k → ℕ) → ℝ) :
    (∑ n ∈ Finset.Ioc N (2 * N), if n % W = v_0 % W then
          (∑ d ∈ D.filter (fun d ↦ ∀ i, d i ∣ n + h i), lam d) ^ 2
        else 0) =
    ∑ d ∈ D, ∑ e ∈ D, lam d * lam e * (∑ n ∈ Finset.Ioc N (2 * N),
          if n % W = v_0 % W ∧ ∀ i, Nat.lcm (d i) (e i) ∣ n + h i then 1 else 0) := by
  simpa using lem_expansion_general N W v_0 k h (fun _ ↦ 1) D lam

end PrimeGaps
