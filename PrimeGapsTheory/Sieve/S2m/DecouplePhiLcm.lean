/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.DecoupleLcm

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Decoupling totients of least common multiples

A coordinatewise identity that decouples reciprocal totients of least common multiples.

## Main results

* `lem_S2m_decouple_phi_lcm`: Expresses the double sum using common-divisor variables and
  separate totient factors.
-/

@[expose] public section

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

/-- Coordinatewise decoupling of `1/φ([dᵢ, eᵢ])` in the `S₂⁽ᵐ⁾` double sum: over weights with
permissible support (positive, squarefree, pairwise-coprime coordinates), the sum of
`λ(d) λ(e) / ∏ᵢ φ([dᵢ, eᵢ])` equals the sum, weighted by `∏ᵢ g(uᵢ)` over common divisors `u`,
of `λ(d) λ(e) / ∏ᵢ φ(dᵢ) φ(eᵢ)`, under the shared cross-coprimality-and-`d m = e m = 1` guard. -/
@[pg_tag "bg246" "lem_S2m_decouple_phi_lcm"]
theorem lem_S2m_decouple_phi_lcm {k : ℕ} (m : Fin k)
    (D : Finset (Fin k → ℕ)) (lam : (Fin k → ℕ) → ℝ)
    (hsupp : ∀ t, lam t ≠ 0 →
      (∀ i, 0 < t i) ∧ (∀ i, Squarefree (t i)) ∧ (∀ i j, i ≠ j → Nat.Coprime (t i) (t j))) :
    (∑ d ∈ D, ∑ e ∈ D, if ((∀ i j, i ≠ j → Nat.Coprime (d i) (e j)) ∧ d m = 1 ∧ e m = 1)
        then lam d * lam e / (∏ i, (Nat.totient (Nat.lcm (d i) (e i)) : ℝ)) else 0)
      =
    ∑ d ∈ D, ∑ e ∈ D, (∑ u ∈ Fintype.piFinset (fun i ↦ (Nat.gcd (d i) (e i)).divisors),
            (∏ i, (g (u i) : ℝ))) *
        (if ((∀ i j, i ≠ j → Nat.Coprime (d i) (e j)) ∧ d m = 1 ∧ e m = 1)
            then lam d * lam e / (∏ i, ((Nat.totient (d i) : ℝ) * Nat.totient (e i)))
            else 0) :=
  lem_decouple_general (fun d e ↦ (∀ i j, i ≠ j → Nat.Coprime (d i) (e j)) ∧ d m = 1 ∧ e m = 1)
    (fun n ↦ (Nat.totient n : ℝ)) (fun u ↦ (g u : ℝ)) D lam hsupp
    fun a b hsa hsb ha hb ↦ by
      simpa using congrArg (fun q : ℚ ↦ (q : ℝ)) (lem_lcm_phi_split a b hsa hsb ha hb)

end PrimeGaps
