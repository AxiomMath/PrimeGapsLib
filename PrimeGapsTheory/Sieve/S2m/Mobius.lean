/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.FunctionG
public import PrimeGapsTheory.Sieve.Common.Decoupling
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Möbius inversion in the second-moment sum

Applies coordinatewise Möbius inversion to the decoupled second-moment sum.

## Main results

* `lem_S2m_mobius`: Rewrites the common-divisor sum using Möbius-weighted variables.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open LemS1RestrictSij in
/-- Möbius-inversion identity for `S₂^{(m)}`: the cross-coprimality guard
`∀ i ≠ j, Nat.Coprime (d i) (e j)` on the left equals, on the right, an inner sum over
`s ∈ sDomain d e` of `∏_{p ∈ offDiag} μ (s p.1 p.2)`. Purely algebraic; holds for arbitrary `D`
and `lam`. -/
@[pg_tag "bg246" "lem_S2m_mobius"]
theorem lem_S2m_mobius {k : ℕ} (m : Fin k) (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ) :
    (∑ d ∈ D, ∑ e ∈ D, (∑ u ∈ uDomain d e, (∏ i, (g (u i) : ℝ))) *
        (if ((∀ i j, i ≠ j → Nat.Coprime (d i) (e j)) ∧ d m = 1 ∧ e m = 1)
            then lam d * lam e / (∏ i, ((Nat.totient (d i) : ℝ) * Nat.totient (e i))) else 0))
      =
    ∑ d ∈ D, ∑ e ∈ D, ∑ u ∈ uDomain d e, ∑ s ∈ sDomain d e,
        (∏ i, (g (u i) : ℝ)) * (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            ((μ (s p.1 p.2) : ℤ) : ℝ)) * (if (d m = 1 ∧ e m = 1)
            then lam d * lam e / (∏ i, ((Nat.totient (d i) : ℝ) * Nat.totient (e i))) else 0) := by
  refine Finset.sum_congr rfl fun d _ ↦ Finset.sum_congr rfl fun e _ ↦ ?_
  set W : ℝ := lam d * lam e / (∏ i, ((Nat.totient (d i) : ℝ) * Nat.totient (e i)))
  set G : ℝ := ∑ u ∈ uDomain d e, (∏ i, (g (u i) : ℝ)) with hG
  have hrhs : (∑ u ∈ uDomain d e, ∑ s ∈ sDomain d e,
        (∏ i, (g (u i) : ℝ)) * (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            ((μ (s p.1 p.2) : ℤ) : ℝ)) *
        (if (d m = 1 ∧ e m = 1) then W else 0)) = G *
        (∑ s ∈ sDomain d e, (∏ p ∈ (Finset.univ.offDiag : Finset (Fin k × Fin k)),
            ((μ (s p.1 p.2) : ℤ) : ℝ))) *
        (if (d m = 1 ∧ e m = 1) then W else 0) := by
    rw [hG, Finset.sum_mul, Finset.sum_mul]
    exact Finset.sum_congr rfl fun u _ ↦ by rw [Finset.mul_sum, Finset.sum_mul]
  rw [hrhs, msum d e]
  by_cases hc : (∀ (i j : Fin k), i ≠ j → (d i).Coprime (e j)) <;>
    by_cases hde : (d m = 1 ∧ e m = 1) <;> simp [hc, hde]

end PrimeGaps
