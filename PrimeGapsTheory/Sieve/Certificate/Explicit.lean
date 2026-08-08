/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.MaynardG


/-! # Explicit certificate of `M_k > 4`

Closed-form rational values of the quadratic forms `I_k` and `J_k^0` on the basis monomials
`(1 - P₁)^b P₂^c`, and the notion of an explicit witness for `M_k > 4` built from them.

## Main definitions

* `PrimeGaps.IExplicit`: the closed form of `∫_{R_k} (1 - P₁)^b P₂^c`.
* `PrimeGaps.JExplicit`: the closed form of `J_k^0` on a pair of basis monomials.
* `PrimeGaps.CertificateExplicit`: a rational linear combination witnessing `M_k > 4`.
-/

@[expose] public section

open Finset Nat

namespace PrimeGaps

/-- The closed-form value of `∫_{R_k} (1 - P₁)^b P₂^c`. -/
noncomputable def IExplicit (k b c : ℕ) : ℚ := b ! * G[c, 2] k / (k + b + 2 * c)!

/-- The coefficient of the `(c₁, c₂)`-term in the double sum defining `JExplicit`.

Writing `A = bi + 2 * ci - 2 * c₁ + 1` and `B = bj + 2 * cj - 2 * c₂ + 1` for the degrees carried by
the two marginals, this is `bi ! * bj ! * (2 * ci - 2 * c₁)! * (2 * cj - 2 * c₂)!` times
`(A + B)! / (A ! * B !)`. The apparent quotient is therefore integral: it is the binomial
coefficient `(A + B).choose A`, as recorded by `gammaInt` and proved by `gammaInt_cast`. -/
def gamma (bi bj ci cj c₁ c₂ : ℕ) : ℚ :=
  bi ! * bj ! * (2 * ci - 2 * c₁)! * (2 * cj - 2 * c₂)! *
    (bi + bj + 2 * ci + 2 * cj - 2 * c₁ - 2 * c₂ + 2)! /
  ((bi + 2 * ci - 2 * c₁ + 1)! * (bj + 2 * cj - 2 * c₂ + 1)!)

/-- The closed-form value of `J_k^0 ((1 - P₁)^b₁ P₂^c₁, (1 - P₁)^b₂ P₂^c₂)`. -/
noncomputable def JExplicit (k b₁ b₂ c₁ c₂ : ℕ) : ℚ :=
  (∑ c₁' ∈ range (c₁ + 1), ∑ c₂' ∈ range (c₂ + 1),
    (c₁.choose c₁' * c₂.choose c₂' * gamma b₁ b₂ c₁ c₂ c₁' c₂' * G[c₁' + c₂', 2] (k - 1))) /
  (k + b₁ + b₂ + 2 * c₁ + 2 * c₂ + 1)!

/-- A witness of `M_k > 4`, in the form of a linear combination `∑ i, a i • (1 - P₁)^(b i) P₂^(c i)`
whose ratio of quadratic forms `k * J_k^0 / I_k` exceeds `4`. -/
structure CertificateExplicit (k : ℕ) where
  /-- The number of basis monomials carrying a coefficient. -/
  N : ℕ
  /-- The exponent of `1 - P₁` in the `i`-th basis monomial. -/
  b : Fin N → ℕ
  /-- The exponent of `P₂` in the `i`-th basis monomial. -/
  c : Fin N → ℕ
  /-- The coefficient of the `i`-th basis monomial. -/
  a : Fin N → ℚ
  /-- The witnessing inequality `4 * I_k < k * J_k^0`, which gives `M_k > 4`. -/
  cert : 4 * ∑ i, ∑ j, a i * a j * IExplicit k (b i + b j) (c i + c j) <
    k * ∑ i, ∑ j, a i * a j * JExplicit k (b i) (b j) (c i) (c j)

end PrimeGaps
