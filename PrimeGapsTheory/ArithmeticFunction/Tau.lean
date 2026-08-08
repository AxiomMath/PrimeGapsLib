/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import PrimeGapsTheory.Discrete.FinMulAntidiag
public import PrimeGapsTheory.ForMathlib.IsMultiplicativeOn
public import PrimeGapsTheory.ForMathlib.NumberTheory.ArithmeticFunction.Defs

import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
import PrimeGapsTheory.ArithmeticFunction.Basic
import PrimeGapsTheory.ForMathlib.Data.Nat.Choose.Basic
import PrimeGapsTheory.Tactic.PaperTag

/-!
# The `r`-fold divisor counting function

This file defines the `r`-fold divisor counting function `τ r` and its specialisation
`τ₂ := τ 2` to the ordinary divisor counting function, develops its combinatorial and
arithmetic properties, and establishes the associated L-series and Euler product
identities on the right half-plane `1 < re s`.

## Main definitions

* `ArithmeticFunction.tau` / `τ r`: the `r`-fold Dirichlet convolution `ζ ^ r` of
  the zeta arithmetic function. By construction `τ 0 = 1` and `τ 1 = ζ`.
* `ArithmeticFunction.tau₂` / `τ₂`: the divisor counting function, defined as `τ 2`.

## Notation

* `τ r` denotes `ArithmeticFunction.tau r`, scoped in `ArithmeticFunction.tau`.
* `τ₂` denotes `ArithmeticFunction.tau₂`, scoped in `ArithmeticFunction.tau` and
  `ArithmeticFunction.tau₂`.

## Main results

* `tau_apply_eq_card_finMulAntidiag`: combinatorial description of `τ r n` as the
  cardinality `#(r.finMulAntidiag n)` of the set of `r`-tuples of naturals whose product
  is `n`.
* `tau_prime_pow` and `tau_prime`: closed forms on prime powers and on primes,
  `τ r (p ^ a) = r.multichoose a` and `τ r p = r`, the stars-and-bars counts.
* `isMultiplicative_tau` and `isSubmultiplicative_tau`: `τ r` is multiplicative, and it is
  submultiplicative on arbitrary pairs.
* `tau_sq_eq_tau_sq`: on squarefree `n`, `τ r n ^ 2 = τ (r ^ 2) n`.
* `LSeries_tau_eq_riemannZeta_pow`, `LSeriesSummable_tau`,
  `LSeriesHasSum_tau_riemannZeta_pow`: on `1 < re s`, the L-series `L(τ r, s)` converges
  absolutely and equals `riemannZeta s ^ r`; their `τ₂`-specialisations are also provided.
* `tau_eulerProduct` and `tau_eulerProduct'`: the Euler product
  `∏ p prime, (1 - p^(-s)) ^ (-r)  =  L(τ r, s)`, in both the `zpow (-r : ℤ)` form
  and the `(_)⁻¹ ^ r` form, with `Multipliable` and `HasProd` companions.
-/

@[expose] public section

open Finset ArithmeticFunction Nat zeta

namespace ArithmeticFunction

/-- The `r`-fold divisor counting function `τ r n` denotes the number of ordered `r`-tuples of
nonzero natural numbers whose product is `n`.

It is a notation for (i.e. syntactically equal to) the `r`-fold Dirichlet convolution of
`ArithmeticFunction.zeta`, and is shown in `tau_apply_eq_card_finMulAntidiag` to satisfy the
description above. In particular, `τ 0 = 1` and `τ 1 = ζ`. -/
@[pg_tag "bg246" "def_tau_r"]
scoped notation:max "τ " r:max => (ζ ^ r : ArithmeticFunction ℕ)

/-- The divisor counting function `τ₂ n` counts the number of divisors of `n` (except `τ₂ 0 = 0`).

It is a notation for (i.e. syntactically equal to) `ζ ^ 2`. -/
scoped notation:max "τ₂" => τ 2

section delab

open Lean PrettyPrinter Delaborator SubExpr Qq

/-- Delaborator for `τ r` and `τ₂`. -/
@[app_delab HPow.hPow]
meta def delabTau : Delab := do
  let ⟨1, ~q(ArithmeticFunction ℕ), ~q(ζ ^ $r)⟩ ← inferTypeQ (← getExpr) | failure
  let rD ← delab r
  match r with
  | ~q(2) => `(τ₂)
  | _ => `(τ $rD)

/-- Delaborator for `τ r n` and `τ₂ n`. -/
@[app_delab DFunLike.coe]
meta def delabTauApply : Delab := do
  let ⟨1, ~q(ℕ), ~q((ζ ^ $r) $n)⟩ ← inferTypeQ (← getExpr) | failure
  let rD ← delab r
  let nD ← delab n
  match r with
  | ~q(2) => `(τ₂ $nD)
  | _ => `(τ $rD $nD)

end delab

@[pg_tag "bg246" "def_tau_r"]
lemma tau_apply_eq_card_finMulAntidiag {r n : ℕ} : (τ r) n = #(r.finMulAntidiag n) := by
  induction r generalizing n with
  | zero => simp [apply_ite, one_apply]
  | succ r ih =>
    obtain rfl | hn := eq_or_ne n 0
    · simp
    obtain rfl | hr := eq_or_ne r 0
    · simp [apply_ite]
    rw [pow_succ, mul_apply, card_eq_sum_card_image (· <| .last r),
      image_finMulAntidiag_apply (by grind), sum_divisorsAntidiagonal' (τ r · * ζ ·)]
    refine sum_congr rfl fun a ha ↦ ?_
    rw [mem_divisors] at ha
    simp_rw [finMulAntidiag_filter_apply_eq, if_pos ha.1, card_map, ih,
      zeta_apply_ne (ne_zero_of_dvd_ne_zero hn ha.1), mul_one]

@[pg_tag "bg246" "lem_tau_submultiplicative"]
theorem isMultiplicative_tau {r : ℕ} : (τ r).IsMultiplicative := by aesop

theorem isSubmultiplicative_zeta : (ζ).IsSubmultiplicative := fun _ _ ↦ by grind [zeta_apply]

/-- `τ r` is submultiplicative: `τ r (a * b) ≤ τ r a * τ r b`. -/
@[pg_tag "bg246" "lem_tau_submultiplicative"]
theorem isSubmultiplicative_tau (r : ℕ) : (τ r).IsSubmultiplicative := isSubmultiplicative_zeta.pow

@[simp] theorem tau_prime_pow {r p a : ℕ} (hp : p.Prime) : τ r (p ^ a) = r.multichoose a := by
  rw [tau_apply_eq_card_finMulAntidiag, finMulAntidiag_prime_pow hp,
    antidiagonalTuple_eq_map_finsuppAntidiag, card_map, card_map,
    card_finsuppAntidiag_nat_eq_multichoose, Finset.card_univ, Fintype.card_fin]

@[simp] theorem tau_prime {r p : ℕ} (hp : p.Prime) : (τ r) p = r := by
  rw [← pow_one p, tau_prime_pow hp, multichoose_one_right]

theorem tau₂_prime_pow {p : ℕ} (hp : p.Prime) (a : ℕ) : τ₂ (p ^ a) = a + 1 := by
  simp [tau_prime_pow hp]

@[pg_tag "bg246" "lem_tau_squared"]
lemma tau_sq_eq_tau_sq {n r : ℕ} (hn : Squarefree n) : τ r n ^ 2 = τ (r ^ 2) n := by
  rw [← isMultiplicative_tau.prod_primeFactors hn, ← isMultiplicative_tau.prod_primeFactors hn,
    ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun p hp ↦ by aesop

@[simp] lemma tau_eq_zero_iff {r n : ℕ} : τ r n = 0 ↔ n = 0 ∨ r = 0 ∧ n ≠ 1 := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  obtain rfl | hr := eq_or_ne r 0
  · simp [one_apply, hn]
  simp_rw [hn, hr, false_and, false_or, iff_false, ← ne_eq]
  rw [isMultiplicative_tau.multiplicative_factorization _ hn]
  aesop

/-- `τ r n` is positive whenever `n` and `r` are nonzero. Both hypotheses are needed:
`τ r 0 = 0`, and `τ 0 n = 0` for `n ≠ 1`. -/
theorem tau_pos {r n : ℕ} (hn : n ≠ 0) (hr : r ≠ 0) : 0 < τ r n := by
  simp [Nat.pos_iff_ne_zero, hn, hr]

section LSeries

open scoped LSeries.notation

/-- The L-series of `τ r` converges absolutely on the right half-plane `1 < re s`. -/
theorem LSeriesSummable_tau {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n : ℕ ↦ (τ r) n) s := by
  induction r with
  | zero =>
    refine summable_of_ne_finset_zero (s := {1}) fun b hb ↦ ?_
    simp [LSeries.term_def, Finset.notMem_singleton.mp hb]
  | succ r ih =>
    refine (LSeriesSummable_congr s (g := ↗((τ r) : ArithmeticFunction ℂ) ⍟
      ((ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ)) fun {n} _ ↦ ?_).mpr
      (LSeriesSummable.convolution ih (LSeriesSummable_zeta_iff.2 hs))
    rw [coe_mul, ← natCoe_mul, ← pow_succ, natCoe_apply]

lemma LSeries.delta_def : δ = fun n ↦ if n = 1 then 1 else 0 := rfl

lemma LSeries.coe_def (f : ArithmeticFunction ℕ) : ↗f = natCoe.coe f := rfl

/-- The L-series of `τ r` is the `r`th power of `riemannZeta` on the right half-plane `1 < re s`. -/
theorem LSeries_tau_eq_riemannZeta_pow {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun (n : ℕ) ↦ (τ r) n) s = (riemannZeta s) ^ r := by
  induction r with
  | zero => simp [one_apply, ← LSeries.delta_def, LSeries_delta]
  | succ r ih =>
    simp_rw [← natCoe_apply] at ih ⊢
    rw [pow_succ, natCoe_mul, ← coe_mul, LSeries_convolution' _ _, ih,
      ← LSeries.coe_def, LSeries_zeta_eq_riemannZeta hs, pow_succ]
    · exact LSeriesSummable_tau hs
    · exact LSeriesSummable_zeta_iff.2 hs

/-- The L-Series of `τ r` at `s` evaluates to `(riemannZeta s) ^ r` whenever `1 < re s`. -/
theorem LSeriesHasSum_tau_riemannZeta_pow {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun (n : ℕ) ↦ (τ r) n) s ((riemannZeta s) ^ r) := by
  rw [← LSeries_tau_eq_riemannZeta_pow hs]
  exact (LSeriesSummable_tau hs).hasSum

/-- The L-series of `τ₂` converges absolutely on the right half-plane `1 < re s`. -/
theorem LSeriesSummable_tau₂ {s : ℂ} (hs : 1 < s.re) : LSeriesSummable (fun n : ℕ ↦ τ₂ n) s :=
  LSeriesSummable_tau hs

/-- The L-Series of `τ₂` at `s` equals `(riemannZeta s) ^ 2` whenever `1 < re s`. -/
theorem LSeries_tau₂_eq_riemannZeta_sq {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n : ℕ ↦ τ₂ n) s = (riemannZeta s) ^ 2 :=
  LSeries_tau_eq_riemannZeta_pow hs

/-- The L-Series of `τ₂` at `s` evaluates to `(riemannZeta s) ^ 2` whenever `1 < re s`. -/
theorem LSeriesHasSum_tau₂_riemannZeta_sq {s : ℂ} (hs : 1 < s.re) :
    LSeriesHasSum (fun n : ℕ ↦ τ₂ n) s ((riemannZeta s) ^ 2) :=
  LSeriesHasSum_tau_riemannZeta_pow hs

end LSeries

section EulerProduct

/-- The Euler product of `τ r`: multipliability of the coefficients, stated as inverses to the
`r`th power. -/
theorem tau_eulerProduct_multipliable' {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : Primes ↦ ((1 - (p : ℂ) ^ (-s)) : ℂ)⁻¹ ^ r) :=
  (riemannZeta_eulerProduct_hasProd hs).multipliable.pow r

/-- The Euler product of `τ r`: `tprod` version, with coefficients stated as inverses to the `r`th
power. -/
theorem tau_eulerProduct' {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Primes, ((1 - (p : ℂ) ^ (-s)) : ℂ)⁻¹ ^ r = LSeries (fun (n : ℕ) ↦ (τ r) n) s := by
  rw [LSeries_tau_eq_riemannZeta_pow hs, ← riemannZeta_eulerProduct_tprod hs]
  exact (riemannZeta_eulerProduct_hasProd hs).multipliable.tprod_pow r

/-- The Euler product of `τ r`: `HasProd` version, with coefficients stated as inverses to the `r`th
power. -/
theorem tau_eulerProduct_hasProd' {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ ((1 - (p : ℂ) ^ (-s)) : ℂ)⁻¹ ^ r)
      (LSeries (fun (n : ℕ) ↦ (τ r) n) s) := by
  rw [← tau_eulerProduct' hs]
  exact (tau_eulerProduct_multipliable' hs).hasProd

/-- The Euler product of `τ r`: multipliability of the coefficients, stated in terms of the `-r`th
power. -/
theorem tau_eulerProduct_multipliable {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    Multipliable (fun p : Primes ↦ ((1 - (p : ℂ) ^ (-s)) : ℂ) ^ (-r : ℤ)) := by
  simpa [zpow_neg, zpow_natCast, ← inv_pow] using tau_eulerProduct_multipliable' hs

/-- The Euler product of `τ r`: `tprod` version, with coefficients stated in terms of the `-r`th
power. -/
theorem tau_eulerProduct {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    ∏' p : Primes, ((1 - (p : ℂ) ^ (-s)) : ℂ) ^ (-r : ℤ) = LSeries (fun (n : ℕ) ↦ (τ r) n) s := by
  simpa [zpow_neg, zpow_natCast, ← inv_pow] using tau_eulerProduct' hs

/-- The Euler product of `τ r`: `HasProd` version, with coefficients stated in terms of the `-r`th
power. -/
theorem tau_eulerProduct_hasProd {r : ℕ} {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Primes ↦ ((1 - (p : ℂ) ^ (-s)) : ℂ) ^ (-r : ℤ))
      (LSeries (fun (n : ℕ) ↦ (τ r) n) s) := by
  rw [← tau_eulerProduct hs]
  exact (tau_eulerProduct_multipliable hs).hasProd

end EulerProduct

end ArithmeticFunction
