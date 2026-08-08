/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Data.Nat.GCD.Prime
public import Mathlib.Data.Rat.Star
public import PrimeGapsTheory.ArithmeticFunction.FunctionG

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Totient identities for least common multiples

Totient and divisor-sum identities involving greatest common divisors and least common multiples.

## Main results

* `lem_phi_lcm_product`: A product identity for totients of an LCM and GCD.
* `lem_lcm_phi_split`: A totient decomposition over least common multiples.
* `lem_lcm_split`: A divisor-sum decomposition over least common multiples.
-/

@[expose] public section

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

/-- If `d * e` is squarefree then `φ([d, e]) * φ((d, e)) = φ(d) * φ(e)`, the
division-free form of `φ([d, e]) = φ(d) * φ(e) / φ((d, e))`. -/
@[pg_tag "bg246" "lem_phi_lcm_product"]
theorem lem_phi_lcm_product (d e : ℕ) (hsq : Squarefree (d * e)) :
    Nat.totient (Nat.lcm d e) * Nat.totient (Nat.gcd d e) =
      Nat.totient d * Nat.totient e := by
  have hcop : Nat.Coprime d e := Nat.coprime_of_squarefree_mul hsq
  rw [Nat.Coprime.gcd_eq_one hcop, Nat.Coprime.lcm_eq_mul hcop, Nat.totient_one, mul_one,
      Nat.totient_mul hcop]

end PrimeGaps

open Nat ArithmeticFunction

namespace Nat

/-- For a squarefree positive natural number `n`,
`φ(n) = ∏ p ∈ n.primeFactors, (p - 1)`. -/
lemma totient_squarefree_prod {n : ℕ} (hn : Squarefree n) (hpos : 0 < n) :
    φ n = ∏ p ∈ n.primeFactors, (p - 1) := by
  rw [Nat.totient_eq_prod_factorization hpos.ne', Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hle : n.factorization p ≤ 1 := hn.natFactorization_le_one p
  have hne : n.factorization p ≠ 0 := Finsupp.mem_support_iff.mp (Nat.support_factorization n ▸ hp)
  simp [show n.factorization p = 1 by omega]

/-- The prime factors of `lcm a b` are the union of the prime factors of `a`
and `b`, provided `a, b ≠ 0`. -/
lemma primeFactors_lcm {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    (a.lcm b).primeFactors = a.primeFactors ∪ b.primeFactors := by
  ext p
  simp only [Nat.mem_primeFactors, Finset.mem_union, Nat.lcm_ne_zero ha hb, ha, hb,
    ne_eq, not_false_eq_true, and_true]
  refine ⟨fun ⟨hp, hpdvd⟩ ↦ (Nat.Prime.dvd_lcm hp).mp hpdvd |>.imp (⟨hp, ·⟩) (⟨hp, ·⟩), ?_⟩
  rintro (⟨hp, h⟩ | ⟨hp, h⟩)
  · exact ⟨hp, h.trans (Nat.dvd_lcm_left a b)⟩
  · exact ⟨hp, h.trans (Nat.dvd_lcm_right a b)⟩

/-- The lcm of two squarefree positive natural numbers is squarefree. -/
lemma squarefree_lcm {d e : ℕ} (hd : Squarefree d) (he : Squarefree e)
    (hdpos : 0 < d) (hepos : 0 < e) : Squarefree (d.lcm e) := by
  rw [Nat.squarefree_iff_factorization_le_one (by positivity : d.lcm e ≠ 0),
    Nat.factorization_lcm hdpos.ne' hepos.ne']
  intro p
  simp only [Finsupp.sup_apply, sup_le_iff]
  exact ⟨hd.natFactorization_le_one p, he.natFactorization_le_one p⟩

/-- For squarefree positive `d`, `e`,
`φ(d) * φ(e) = φ(lcm d e) * φ(gcd d e)`. -/
lemma totient_mul_eq_lcm_mul_gcd
    {d e : ℕ} (hd : Squarefree d) (he : Squarefree e)
    (hdpos : 0 < d) (hepos : 0 < e) :
    Nat.totient d * Nat.totient e =
      Nat.totient (Nat.lcm d e) * Nat.totient (Nat.gcd d e) := by
  rw [totient_squarefree_prod hd hdpos, totient_squarefree_prod he hepos,
    totient_squarefree_prod (squarefree_lcm hd he hdpos hepos) (Nat.lcm_pos hdpos hepos),
    totient_squarefree_prod (hd.squarefree_of_dvd (Nat.gcd_dvd_left d e))
      (Nat.gcd_pos_of_pos_left e hdpos),
    primeFactors_lcm hdpos.ne' hepos.ne',
    Nat.primeFactors_gcd hdpos.ne' hepos.ne']
  exact Finset.prod_union_inter.symm

/-- A product of pairwise distinct primes is squarefree. -/
lemma squarefree_prod_of_forall_prime {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) :
    Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ fun p hp ↦ (hS p hp).squarefree
  intro p hp q hq hpq
  exact Nat.coprime_iff_isRelPrime.mp
    ((Nat.coprime_primes (hS p (Finset.mem_coe.mp hp)) (hS q (Finset.mem_coe.mp hq))).mpr hpq)

/-- For squarefree positive `n`, the totient cast to `ℤ` equals
`∏ p ∈ n.primeFactors, (p - 1 : ℤ)`. -/
lemma totient_squarefree_eq_prod {n : ℕ} (hn : Squarefree n) (hnpos : 0 < n) :
    (Nat.totient n : ℤ) = ∏ p ∈ n.primeFactors, (p - 1 : ℤ) := by
  rw [totient_squarefree_prod hn hnpos, Nat.cast_prod]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hp2 : 2 ≤ p := (Nat.prime_of_mem_primeFactors hp).two_le
  rw [Nat.cast_sub (by omega)]
  simp

end Nat

namespace PrimeGaps

/-- For squarefree positive `d`, `e`,
`1 / φ([d, e]) = (1 / (φ(d) · φ(e))) · ∑_{u | (d, e)} g(u)`. -/
@[pg_tag "bg246" "lem_lcm_phi_split"]
theorem lem_lcm_phi_split (d e : ℕ) (hd : Squarefree d) (he : Squarefree e)
    (hdpos : 0 < d) (hepos : 0 < e) :
    (1 : ℚ) / (Nat.totient (Nat.lcm d e)) = (1 : ℚ) / (Nat.totient d * Nat.totient e) *
      (∑ u ∈ (Nat.gcd d e).divisors, (g u : ℚ)) := by
  have hφd_ne : (Nat.totient d : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hdpos).ne'
  have hφe_ne : (Nat.totient e : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr hepos).ne'
  have hφlcm_ne : (Nat.totient (Nat.lcm d e) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.totient_pos.mpr (Nat.lcm_pos hdpos hepos)).ne'
  rw [show (∑ u ∈ (Nat.gcd d e).divisors, (g u : ℚ)) = (Nat.totient (Nat.gcd d e) : ℚ) from
    mod_cast ArithmeticFunction.sum_divisors_detotient]
  field_simp
  linarith [show (Nat.totient d * Nat.totient e : ℚ) =
    Nat.totient (Nat.lcm d e) * Nat.totient (Nat.gcd d e) from
      mod_cast totient_mul_eq_lcm_mul_gcd hd he hdpos hepos]

/-- `1/[d, e] = (1/(d·e)) · ∑_{u | (d, e)} φ(u)`, for positive `d, e`. -/
@[pg_tag "bg246" "lem_lcm_split"]
theorem lem_lcm_split (d e : ℕ) (hdpos : 0 < d) (hepos : 0 < e) : (1 : ℚ) / (Nat.lcm d e) =
      (1 : ℚ) / (d * e) *
      (∑ u ∈ (Nat.gcd d e).divisors, (Nat.totient u : ℚ)) := by
  rw [show (∑ u ∈ (Nat.gcd d e).divisors, (Nat.totient u : ℚ)) = (Nat.gcd d e : ℚ) from
    mod_cast Nat.sum_totient (Nat.gcd d e)]
  have hlcm : (Nat.lcm d e : ℚ) ≠ 0 := mod_cast (Nat.lcm_pos hdpos hepos).ne'
  field_simp
  linarith [show (Nat.gcd d e : ℚ) * (Nat.lcm d e : ℚ) = (d : ℚ) * e from
    mod_cast Nat.gcd_mul_lcm d e]

end PrimeGaps
