/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SijOne
public import PrimeGapsTheory.Sieve.S2m.Substitution
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Bounding the unit-index coupling terms

Bounds the coupling terms in which an auxiliary index is one.

## Main results

* `lem_S2m_sij_one`: Bounds the unit-index coupling contribution.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open LemS1RestrictSij in
/-- Restricting `ymWeightedSum` to the single tuple `sᵢⱼ = 1` for all `i ≠ j`, the
`(X_N / φ(W))`-scaled contribution equals the prefactor times the `u`-sum of
`y⁽ᵐ⁾(u)² / ∏ᵢ g(uᵢ)`. On the squarefree support `μ(uᵢ)² = 1`; off it `ym` vanishes. -/
@[pg_tag "bg246" "lem_S2m_sij_one"]
theorem lem_S2m_sij_one {k : ℕ} (N W : ℕ) (m : Fin k) (lam : (Fin k → ℕ) →₀ ℝ) :
    ((Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient W : ℝ)) *
      (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
            (∏ i, (μ (u i) : ℝ) ^ 2 / (g (u i) : ℝ)) *
            ym m lam u * ym m lam u
          else 0)
      =
    ((Nat.primeCountingIoc N (2 * N) : ℝ) / (Nat.totient W : ℝ)) *
      (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
            ym m lam u ^ 2 / (∏ i, (g (u i) : ℝ))
          else 0) := by
  refine mul_tsum_mobiusSq_weight_mul_self _ (fun n ↦ (g n : ℝ)) (ym m lam) _ fun u ↦
    or_iff_not_imp_left.mpr fun hsq ↦ ?_
  obtain ⟨i₀, hi₀⟩ := not_forall.mp hsq
  rw [ym_apply']
  push_cast
  rw [Finset.prod_eq_zero (Finset.mem_univ i₀)] <;>
    simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hi₀]

end PrimeGaps
