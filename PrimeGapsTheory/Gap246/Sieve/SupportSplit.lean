/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.PermissibleSupport.FunctionW
public import PrimeGapsTheory.Sieve.SieveTruncation


/-!
# The ε-enlarged sieve support and the divisor-sum split

The sieve weights of the enlarged variational problem are supported on divisor
tuples with product up to `R^{1+ε}` (rather than `R`); the analysis then splits
each weight through the "small remaining product" cutoff `R^{1-ε}`.  This file sets
up those combinatorial objects and proves the elementary pointwise inequality
(`lem_pointwise`) behind the sieve lower bound.

* `epsPermissible` — support constraint `def_adm_support` with the enlarged bound `R^{1+ε}`.
* `lambdaSplit1` / `lambdaSplit2` — the split `λ = λ_{1,m} + λ_{2,m}` (`def_split`).
* `Asum` — the divisor sum `A_{ℓ,m}` (`not_a`).
* `lem_pointwise` — `(x₁+x₂)² ≥ x₁² + 2x₁x₂`.
-/

@[expose] public section

open scoped BigOperators PrimeGaps.sieveModulus
open PrimeGaps

namespace Gaps246

/-- **`def_adm_support`.** The ε-enlarged support constraint on the sieve weights `λ`:
`λ(d) = 0` unless every `d_i ≥ 1`, the product `∏ d_i` is at most `R^{1+ε}`
(where `R = sieveTruncation N δ θ`), `gcd(∏ d_i, W N) = 1`, and `∏ d_i` is
squarefree. Mirrors `HasPermissibleSupport` with the bound `R` relaxed to
`R^{1+ε}`. -/
def epsPermissible (k N : ℕ) (δ θ ε : ℝ) (lam : (Fin k → ℕ) → ℝ) : Prop :=
  ∀ d : Fin k → ℕ, ¬ ((∀ i, 1 ≤ d i) ∧ (∏ i, d i : ℝ) ≤ (sieveTruncation N δ θ) ^ (1 + ε) ∧
        Nat.Coprime (∏ i, d i) (W N) ∧ Squarefree (∏ i, d i)) →
      lam d = 0

/-- The support conditions of an `ε`-permissible weight, read off where it does not vanish. -/
theorem epsPermissible_conditions {k N : ℕ} {δ θ ε : ℝ} {lam : (Fin k → ℕ) → ℝ}
    (hp : epsPermissible k N δ θ ε lam) {d : Fin k → ℕ} (hd : lam d ≠ 0) :
    (∀ i, 1 ≤ d i) ∧ (∏ i, d i : ℝ) ≤ (sieveTruncation N δ θ) ^ (1 + ε) ∧
      Nat.Coprime (∏ i, d i) (W N) ∧ Squarefree (∏ i, d i) := by
  by_contra hc
  exact hd (hp d hc)

/-- **`def_split`.** The first piece `λ_{1,m}` of the divisor-sum split: keep `λ(d)`
when the product of the coordinates *other than* `m` is at most `R^{1-ε}`, and zero
it otherwise. -/
noncomputable def lambdaSplit1 (k N : ℕ) (δ θ ε : ℝ) (m : Fin k)
    (lam : (Fin k → ℕ) → ℝ) (d : Fin k → ℕ) : ℝ :=
  lam d * (if (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ (sieveTruncation N δ θ) ^ (1 - ε)
      then 1 else 0)

/-- **`def_split2`.** The complementary piece `λ_{2,m} = λ − λ_{1,m}`. -/
noncomputable def lambdaSplit2 (k N : ℕ) (δ θ ε : ℝ) (m : Fin k)
    (lam : (Fin k → ℕ) → ℝ) (d : Fin k → ℕ) : ℝ :=
  lam d - lambdaSplit1 k N δ θ ε m lam d

/-- **`not_a`.** The divisor sum `A_{ℓ,m}(n) = ∑_{d_i | n + h_i} λ_{ℓ,m}(d)`, realised
(as in `GPYSieveS1.innerDivSum`) as a `tsum` over positive tuples `d` with
`(d_i : ℤ) ∣ (n + h_i)` for all `i`.  The index `ℓ ∈ {1, 2}` selects the split
piece; because `λ` has finite support the sum is finite. -/
noncomputable def Asum (k N : ℕ) (δ θ ε : ℝ) (ℓ : ℕ) (m : Fin k) (h : Fin k → ℕ)
    (lam : (Fin k → ℕ) → ℝ) (n : ℤ) : ℝ :=
  ∑' d : Fin k → ℕ, (if (∀ i, 1 ≤ d i) ∧ (∀ i, (d i : ℤ) ∣ (n + h i)) then
        (if ℓ = 1 then lambdaSplit1 k N δ θ ε m lam d
          else lambdaSplit2 k N δ θ ε m lam d)
      else 0)

/-- **`lem_pointwise`.** The elementary inequality driving the sieve lower bound:
`(x₁ + x₂)² ≥ x₁² + 2 x₁ x₂`, i.e. dropping the nonnegative `x₂²`. -/
theorem lem_pointwise (x₁ x₂ : ℝ) : (x₁ + x₂) ^ 2 ≥ x₁ ^ 2 + 2 * x₁ * x₂ := by
  nlinarith [sq_nonneg x₂]

end Gaps246
