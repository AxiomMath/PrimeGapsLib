/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import Mathlib.NumberTheory.LSeries.HurwitzZetaValues

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Euler products

Euler-product identities for zeta values and Möbius divisor sums.

## Main definitions

* `zetaTwo`: The value of the zeta function at two.

## Main results

* `eulerProduct_zetaTwo`: The Euler product for `ζ(2)`.
-/

@[expose] public section

open Real

open scoped BigOperators
open Filter Topology

namespace Complex

/-- Transfer of `HasProd` along the inclusion `ℝ → ℂ`: a real family has a product iff its
image under `(↑) : ℝ → ℂ` does. -/
theorem hasProd_ofReal {ι : Type*} {f : ι → ℝ} {a : ℝ} :
    HasProd (fun i ↦ (f i : ℂ)) (a : ℂ) ↔ HasProd f a := by
  have hemb : Topology.IsEmbedding ((↑) : ℝ → ℂ) := Complex.isometry_ofReal.isEmbedding
  unfold HasProd
  rw [hemb.tendsto_nhds_iff]
  constructor <;> exact fun h ↦ h.congr fun s ↦ by simp [Complex.ofReal_prod]

end Complex

namespace PrimeGaps

/-- The value `zeta(2) = ∑_{n ≥ 1} 1/n^2`, taken as the (unconditional) sum over
`ℕ`; the `n = 0` term contributes `1/0^2 = 0`, so it agrees with the sum over
positive integers. -/
noncomputable def zetaTwo : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 2

private lemma cpow_neg_two (p : ℂ) : p ^ (-(2 : ℂ)) = 1 / p ^ 2 := by
  rw [Complex.cpow_neg, Complex.cpow_two]
  simp

private lemma riemannZeta_two_ofReal : riemannZeta 2 = ((Real.pi ^ 2 / 6 : ℝ) : ℂ) := by
  rw [riemannZeta_two]
  push_cast
  ring

/-- **Euler product for `zeta(2)`.** -/
@[pg_tag "bg246" "slem_zeta_2_euler_product"]
theorem eulerProduct_zetaTwo : HasProd (fun p : Nat.Primes ↦ (1 - 1 / (p : ℝ) ^ 2)⁻¹) zetaTwo := by
  have hz : zetaTwo = (π ^ 2 / 6 : ℝ) := hasSum_zeta_two.tsum_eq
  have hcomplex := riemannZeta_eulerProduct_hasProd (s := 2) (by norm_num)
  have hterm : (fun p : Nat.Primes ↦ (1 - (p : ℂ) ^ (-(2 : ℂ)))⁻¹) =
      (fun p : Nat.Primes ↦ (((1 - 1 / (p : ℝ) ^ 2)⁻¹ : ℝ) : ℂ)) := by
    funext p
    rw [cpow_neg_two]
    push_cast
    ring
  rw [riemannZeta_two_ofReal, hterm] at hcomplex
  rw [hz]
  exact Complex.hasProd_ofReal.mp hcomplex

/-- The series `∑_{n ≥ 1} 1/n^2` defining `zeta(2)` converges. -/
@[pg_tag "bg246" "slem_zeta_2_euler_product"]
theorem summable_zetaTwo : Summable (fun n : ℕ ↦ 1 / (n : ℝ) ^ 2) :=
  Real.summable_one_div_nat_pow.mpr (by norm_num)

/-- The product `∏_{p ∈ ℙ} (1 - p^{-2})^{-1}` converges. -/
@[pg_tag "bg246" "slem_zeta_2_euler_product"]
theorem multipliable_eulerProduct_zetaTwo :
    Multipliable (fun p : Nat.Primes ↦ (1 - 1 / (p : ℝ) ^ 2)⁻¹) :=
  eulerProduct_zetaTwo.multipliable

/-- The infinite product interpreted as the limit of its finite partial products. -/
theorem tendsto_partialProduct_eulerProduct_zetaTwo :
    Tendsto (fun N : ℕ ↦ ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ) ^ 2)⁻¹)
      atTop (𝓝 zetaTwo) := by
  have hemb : Topology.IsEmbedding ((↑) : ℝ → ℂ) := Complex.isometry_ofReal.isEmbedding
  have hz : zetaTwo = (π ^ 2 / 6 : ℝ) := hasSum_zeta_two.tsum_eq
  have hcomplex := riemannZeta_eulerProduct (s := 2) (by norm_num)
  rw [riemannZeta_two_ofReal] at hcomplex
  rw [hz, hemb.tendsto_nhds_iff]
  refine hcomplex.congr fun n ↦ ?_
  simp only [Function.comp_apply, Complex.ofReal_prod]
  refine Finset.prod_congr rfl fun p _ ↦ ?_
  rw [cpow_neg_two]
  push_cast
  ring

/-- For every real number `x` with `x ≠ 1`, `1 + x / (1 - x) = 1 / (1 - x)`.

This is the Euler-factor identity applied at `x = p⁻²` for a prime `p` (where `p ≥ 2`
forces `p⁻² ≤ 1/4 < 1`, so the hypothesis holds). -/
@[pg_tag "bg246" "slem_euler_factor_identity"]
theorem one_add_div_one_sub_eq_one_div (x : ℝ) (hx : x ≠ 1) : 1 + x / (1 - x) = 1 / (1 - x) := by
  have h : (1 : ℝ) - x ≠ 0 := sub_ne_zero.mpr hx.symm
  field_simp
  ring

end PrimeGaps
