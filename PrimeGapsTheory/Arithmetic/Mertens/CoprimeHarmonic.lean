/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Data.Int.Star
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni
public import PrimeGapsTheory.Arithmetic.RemovedPrimes

import PrimeGapsTheory.ArithmeticFunction.Estimates
import PrimeGapsTheory.ForMathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Coprime harmonic sums

A Mertens-type asymptotic for harmonic sums restricted by coprimality.

## Main definitions

* `coprimeReciprocalSum`: The reciprocal sum over integers coprime to a modulus.

## Main results

* `coprime_reciprocal_sum_asymptotic`: The asymptotic formula for the coprime harmonic sum.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius Finset
open Real

namespace ArithmeticFunction

/-- `μ (∏ p ∈ s, p) = ∏ p ∈ s, μ p` for a finset `s` of primes. -/
theorem mu_prod_primes (s : Finset ℕ) (hall : ∀ p ∈ s, p.Prime) :
    (μ (∏ p ∈ s, p) : ℤ) = ∏ p ∈ s, (μ p : ℤ) := by
  apply ArithmeticFunction.IsMultiplicative.map_prod (fun p ↦ p)
    ArithmeticFunction.isMultiplicative_moebius
  intro p hp q hq hpq
  simp only [Function.onFun]
  exact (Nat.coprime_primes (hall p hp) (hall q hq)).mpr hpq

end ArithmeticFunction

namespace Finset

/-- `∑_{s ⊆ P} ∏_{p ∈ s} a p = ∏_{p ∈ P} (1 + a p)`. -/
theorem sum_powerset_prod {ι : Type*} (P : Finset ι) (a : ι → ℝ) :
    ∑ s ∈ P.powerset, (∏ p ∈ s, a p) = ∏ p ∈ P, (1 + a p) := by
  classical
  have h := Finset.prod_add a (fun _ ↦ (1 : ℝ)) P
  simp only [Finset.prod_const_one, mul_one] at h
  rw [← h]
  exact Finset.prod_congr rfl fun p _ ↦ add_comm _ _

/-- For `x ∉ P`, the subsets of `P` are disjoint from the subsets obtained by inserting `x`. -/
theorem disjoint_powerset_image_insert {ι : Type*} [DecidableEq ι] (P : Finset ι) (x : ι)
    (hx : x ∉ P) :
    Disjoint P.powerset (Finset.image (insert x) P.powerset) := by
  rw [Finset.disjoint_left]
  intro s hs hs2
  rw [Finset.mem_powerset] at hs
  rw [Finset.mem_image] at hs2
  obtain ⟨t, ht, rfl⟩ := hs2
  exact hx (hs (Finset.mem_insert_self x t))

/-- Differentiated form of `sum_powerset_prod`:
`∑_{s ⊆ P} (∏_{p ∈ s} a p) (∑_{p ∈ s} b p) = ∑_{q ∈ P} b q * a q * ∏_{p ∈ P.erase q} (1 + a p)`. -/
theorem powerset_deriv {ι : Type*} [DecidableEq ι] (P : Finset ι) (a b : ι → ℝ) :
    ∑ s ∈ P.powerset, (∏ p ∈ s, a p) * (∑ p ∈ s, b p) =
      ∑ q ∈ P, b q * a q * ∏ p ∈ P.erase q, (1 + a p) := by
  induction P using Finset.induction with
  | empty => simp
  | @insert x P hx ih =>
    rw [Finset.powerset_insert, Finset.sum_union (disjoint_powerset_image_insert P x hx)]
    have hinj : ∀ s ∈ P.powerset, ∀ t ∈ P.powerset, insert x s = insert x t → s = t := by
      intro s hs t ht hst
      rw [Finset.mem_powerset] at hs ht
      have hxs : x ∉ s := fun h ↦ hx (hs h)
      have hxt : x ∉ t := fun h ↦ hx (ht h)
      rw [← Finset.erase_insert hxs, ← Finset.erase_insert hxt, hst]
    rw [Finset.sum_image hinj]
    have himg : ∀ s ∈ P.powerset, (∏ p ∈ insert x s, a p) * (∑ p ∈ insert x s, b p) =
          a x * (∏ p ∈ s, a p) * (b x + ∑ p ∈ s, b p) := by
      intro s hs
      rw [Finset.mem_powerset] at hs
      have hxs : x ∉ s := fun h ↦ hx (hs h)
      rw [Finset.prod_insert hxs, Finset.sum_insert hxs, mul_assoc]
    rw [Finset.sum_congr rfl himg]
    have hexp : ∑ s ∈ P.powerset, (a x * ∏ p ∈ s, a p) * (b x + ∑ p ∈ s, b p) =
        a x * b x * (∑ s ∈ P.powerset, ∏ p ∈ s, a p) +
          a x * (∑ s ∈ P.powerset, (∏ p ∈ s, a p) * (∑ p ∈ s, b p)) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun s _ ↦ by ring
    rw [hexp, sum_powerset_prod, ih, Finset.sum_insert hx, Finset.erase_insert hx]
    have hqterm : ∑ q ∈ P, b q * a q * ∏ p ∈ (insert x P).erase q, (1 + a p) =
        ∑ q ∈ P, (1 + a x) * (b q * a q * ∏ p ∈ P.erase q, (1 + a p)) := by
      refine Finset.sum_congr rfl fun q hq ↦ ?_
      rw [Finset.erase_insert_of_ne (by rintro rfl; exact hx hq),
        Finset.prod_insert (fun h ↦ hx (Finset.mem_of_mem_erase h))]
      ring
    rw [hqterm, ← Finset.mul_sum, ← ih]
    ring

end Finset

namespace Nat

/-- For squarefree `m`, the divisors of `m` are exactly the products `∏_{p ∈ s} p` over subsets
`s ⊆ m.primeFactors`. -/
theorem divisors_image_powerset (m : ℕ) (hm : Squarefree m) :
    (m.primeFactors.powerset.image (fun s ↦ ∏ p ∈ s, p)) = m.divisors := by
  ext d
  simp only [Finset.mem_image, Finset.mem_powerset, Nat.mem_divisors]
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨?_, hm.ne_zero⟩
    have h1 : (∏ p ∈ s, p) ∣ (∏ p ∈ m.primeFactors, p) :=
      Finset.prod_dvd_prod_of_subset s m.primeFactors (fun p ↦ p) hs
    rwa [Nat.prod_primeFactors_of_squarefree hm] at h1
  · rintro ⟨hd, hm0⟩
    exact ⟨d.primeFactors, Nat.primeFactors_mono hd hm0,
      Nat.prod_primeFactors_of_squarefree (hm.squarefree_of_dvd hd)⟩

/-- `(∏ p ∈ s, p).primeFactors = s` for a finset `s` of primes. -/
theorem prod_primeFactors_eq (s : Finset ℕ) (hall : ∀ p ∈ s, p.Prime) :
    (∏ p ∈ s, p).primeFactors = s := by
  ext q
  rw [Nat.mem_primeFactors]
  constructor
  · rintro ⟨hqp, hqdvd, hne⟩
    obtain ⟨p, hp, hqp2⟩ := (Nat.Prime.prime hqp).exists_mem_finset_dvd hqdvd
    rwa [(Nat.prime_dvd_prime_iff_eq hqp (hall p hp)).mp hqp2]
  · intro hq
    refine ⟨hall q hq, Finset.dvd_prod_of_mem _ hq, ?_⟩
    intro h0
    rw [Finset.prod_eq_zero_iff] at h0
    obtain ⟨p, hp, hp0⟩ := h0
    exact (hall p hp).ne_zero hp0

/-- Reindex a divisor sum over squarefree `m` as a sum over subsets of `m.primeFactors`:
`∑_{d ∣ m} f d = ∑_{s ⊆ m.primeFactors} f (∏_{p ∈ s} p)`. -/
theorem divisors_sum_powerset (m : ℕ) (hm : Squarefree m) (f : ℕ → ℝ) :
    ∑ d ∈ m.divisors, f d = ∑ s ∈ m.primeFactors.powerset, f (∏ p ∈ s, p) := by
  rw [← divisors_image_powerset m hm, Finset.sum_image]
  intro s hs t ht hst
  rw [Finset.mem_coe, Finset.mem_powerset] at hs ht
  have h1 := prod_primeFactors_eq s fun p hp ↦ Nat.prime_of_mem_primeFactors (hs hp)
  have h2 := prod_primeFactors_eq t fun p hp ↦ Nat.prime_of_mem_primeFactors (ht hp)
  simp only at hst
  rw [← h1, ← h2, hst]

end Nat

namespace PrimeGaps

/-- The left-hand side sum `∑_{k ≤ Z, (k,m)=1} 1/k`, ranging over positive integers
`k` with `1 ≤ k ≤ Z` and `gcd(k, m) = 1`. -/
noncomputable def coprimeReciprocalSum (m : ℕ) (Z : ℝ) : ℝ :=
  ∑ k ∈ {k ∈ Finset.Icc 1 ⌊Z⌋₊ | Nat.Coprime k m}, (1 : ℝ) / k

/-- The harmonic partial sum `∑_{j=1}^{⌊X⌋} 1/j`, the inner sum appearing after Möbius
reindexing. -/
noncomputable def harmonicPartial (X : ℝ) : ℝ := ∑ j ∈ Finset.Icc 1 ⌊X⌋₊, (1 : ℝ) / j

/-- The real cast of the rational harmonic number `harmonic N` equals the explicit partial
sum `∑_{j=1}^{N} 1/j`. -/
theorem harmonic_cast_eq_sum (N : ℕ) : (harmonic N : ℝ) = ∑ j ∈ Finset.Icc 1 N, (1 : ℝ) / j := by
  rw [harmonic_eq_sum_Icc]; push_cast; ring_nf

/-- Harmonic asymptotic at integer points: for every `N ≥ 1`,
`|harmonic N - (log N + γ)| ≤ 1/N`, with absolute constant `1`. -/
theorem harmonic_bound_int (N : ℕ) (hN : 1 ≤ N) :
    |(harmonic N : ℝ) - (Real.log N + Real.eulerMascheroniConstant)| ≤ 1 / N := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (n := N)
  have hseq' := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (n := N)
  unfold Real.eulerMascheroniSeq Real.eulerMascheroniSeq' at *
  have hN0 : N ≠ 0 := by omega
  rw [if_neg hN0] at hseq'
  set A : ℝ := (harmonic N : ℝ) - Real.log N - Real.eulerMascheroniConstant with hA
  have h0A : 0 < A := by rw [hA]; linarith
  have hAupper : A < Real.log ((N : ℝ) + 1) - Real.log N := by rw [hA]; linarith
  have hlogdiff : Real.log ((N : ℝ) + 1) - Real.log N ≤ 1 / N := by
    rw [← Real.log_div (by positivity) (by positivity)]
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
    have hsub : ((N : ℝ) + 1) / N - 1 = 1 / N := by rw [div_sub_one (by positivity)]; ring_nf
    linarith
  rw [show (harmonic N : ℝ) - (Real.log N + Real.eulerMascheroniConstant) = A by rw [hA]; ring,
    abs_of_pos h0A]
  linarith

/-- Harmonic asymptotic at real points `X ≥ 1`:
`|harmonicPartial X - (log X + γ)| ≤ 4/X`, with absolute constant `4`. -/
theorem harmonic_bound_real (X : ℝ) (hX : 1 ≤ X) :
    |harmonicPartial X - (Real.log X + Real.eulerMascheroniConstant)| ≤ 4 / X := by
  set N : ℕ := ⌊X⌋₊ with hNdef
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNle : (N : ℝ) ≤ X := by rw [hNdef]; exact Nat.floor_le hX0
  have hXlt : X < (N : ℝ) + 1 := by rw [hNdef]; exact_mod_cast Nat.lt_floor_add_one X
  have hHP : harmonicPartial X = (harmonic N : ℝ) := by
    rw [harmonicPartial, harmonic_cast_eq_sum]
  have hint := harmonic_bound_int N hN1
  have hXpos : (0 : ℝ) < X := by linarith
  have hlogle : Real.log N ≤ Real.log X := Real.log_le_log hNpos hNle
  have hlogub : Real.log X - Real.log N ≤ 1 / N := by
    have hle : Real.log X ≤ Real.log ((N : ℝ) + 1) := Real.log_le_log hXpos hXlt.le
    have hlog := Real.log_le_sub_one_of_pos (show (0 : ℝ) < ((N : ℝ) + 1) / N by positivity)
    rw [Real.log_div (by positivity) (by positivity)] at hlog
    have hsub : ((N : ℝ) + 1) / N - 1 = 1 / N := by rw [div_sub_one (by positivity)]; ring_nf
    linarith
  have h2NX : X < 2 * N := by
    have h1N : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    linarith
  have hNX : 1 / (N : ℝ) + 1 / (N : ℝ) ≤ 4 / X := by
    rw [show 1 / (N : ℝ) + 1 / N = 2 / N from by ring,
      show (4 : ℝ) / X = 2 / (X / 2) from by rw [div_div_eq_mul_div]; ring]
    gcongr
    linarith
  have hsplit : harmonicPartial X - (Real.log X + Real.eulerMascheroniConstant) =
      ((harmonic N : ℝ) - (Real.log N + Real.eulerMascheroniConstant)) +
        (Real.log N - Real.log X) := by
    rw [hHP]; ring
  rw [hsplit]
  have htri : |((harmonic N : ℝ) - (Real.log N + Real.eulerMascheroniConstant)) +
      (Real.log N - Real.log X)| ≤ |(harmonic N : ℝ) - (Real.log N +
        Real.eulerMascheroniConstant)| +
        |Real.log N - Real.log X| :=
    abs_add_le _ _
  have habs2 : |Real.log N - Real.log X| ≤ 1 / N := by rw [abs_le]; constructor <;> linarith
  linarith

/-- For positive `d`, the reciprocal sum over multiples of `d` up to `⌊Z⌋` equals
`harmonicPartial (Z / d) / d`. -/
theorem sum_one_div_filter_dvd_eq_one_div_mul_harmonicPartial (d : ℕ) (hd : 0 < d) (Z : ℝ) :
    ∑ k ∈ {k ∈ Finset.Icc 1 ⌊Z⌋₊ | d ∣ k}, (1 : ℝ) / k =
      (1 / d) * harmonicPartial (Z / d) := by
  rw [harmonicPartial, Finset.mul_sum]
  rw [show ⌊Z / (d : ℝ)⌋₊ = ⌊Z⌋₊ / d from Nat.floor_div_natCast Z d]
  refine Finset.sum_bij (fun k _ ↦ k / d) (fun k hk ↦ ?_) (fun k1 hk1 k2 hk2 heq ↦ ?_)
    (fun j hj ↦ ?_) (fun k hk ↦ ?_)
  · rw [Finset.mem_filter, Finset.mem_Icc] at hk
    obtain ⟨⟨h1, h2⟩, hdvd⟩ := hk
    exact Finset.mem_Icc.mpr ⟨(Nat.one_le_div_iff hd).mpr (Nat.le_of_dvd (by omega) hdvd),
      Nat.div_le_div_right h2⟩
  · rw [Finset.mem_filter] at hk1 hk2
    have e1 := Nat.div_mul_cancel hk1.2
    have e2 := Nat.div_mul_cancel hk2.2
    rw [heq] at e1
    omega
  · rw [Finset.mem_Icc] at hj
    obtain ⟨hj1, hj2⟩ := hj
    refine ⟨d * j, ?_, Nat.mul_div_cancel_left j hd⟩
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by nlinarith [hj1, hd], ?_⟩, Dvd.intro j rfl⟩
    rw [Nat.le_div_iff_mul_le hd] at hj2
    rw [Nat.mul_comm d j]; exact hj2
  · rw [Finset.mem_filter] at hk
    obtain ⟨c, rfl⟩ := hk.2
    rw [Nat.mul_div_cancel_left _ hd]
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    push_cast
    by_cases hc : c = 0
    · subst hc; simp
    · have hcpos : (0 : ℝ) < c := by exact_mod_cast Nat.pos_of_ne_zero hc
      field_simp

/-- Möbius reindexing of the coprime reciprocal sum: for `m ≥ 1` and any `Z`,
`coprimeReciprocalSum m Z = ∑_{d ∣ m} (μ(d)/d) · harmonicPartial (Z/d)`.

Uses the coprimality indicator `[gcd(k,m) = 1] = ∑_{d ∣ gcd(k,m)} μ(d)`, Fubini over the
finite index sets, and the per-divisor reindexing `k = d·j` from
`sum_one_div_filter_dvd_eq_one_div_mul_harmonicPartial`. -/
theorem coprime_reindex (m : ℕ) (hm : 1 ≤ m) (Z : ℝ) : coprimeReciprocalSum m Z =
      ∑ d ∈ m.divisors, ((μ d : ℝ) / d) * harmonicPartial (Z / d) := by
  have hm0 : m ≠ 0 := by omega
  rw [coprimeReciprocalSum, Finset.sum_filter]
  have hstepB : ∀ k ∈ Finset.Icc 1 ⌊Z⌋₊, (if Nat.Coprime k m then (1 : ℝ) / k else 0) =
        (∑ d ∈ ((Nat.gcd k m).divisors), (μ d : ℝ)) * ((1 : ℝ) / k) := by
    intro k hk
    have hind : ∑ d ∈ ((Nat.gcd k m).divisors), (μ d : ℝ) =
        if Nat.gcd k m = 1 then 1 else 0 := by
      have h2 := congrArg (fun z : ℤ ↦ (z : ℝ))
        (ArithmeticFunction.sum_divisors_moebius (d := Nat.gcd k m))
      push_cast at h2
      rw [h2]
    rw [hind]
    by_cases hc : Nat.Coprime k m
    · rw [if_pos hc, if_pos hc]; ring
    · rw [if_neg hc, if_neg hc]; ring
  rw [Finset.sum_congr rfl hstepB]
  have hstepC : ∀ k ∈ Finset.Icc 1 ⌊Z⌋₊,
      (∑ d ∈ ((Nat.gcd k m).divisors), (μ d : ℝ)) * ((1 : ℝ) / k) =
        (∑ d ∈ {d ∈ m.divisors | d ∣ k}, (μ d : ℝ)) * ((1 : ℝ) / k) := by
    intro k hk
    congr 1
    refine Finset.sum_congr ?_ fun _ _ ↦ rfl
    ext d
    rw [Nat.mem_divisors, Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨hdvd, _⟩
      exact ⟨⟨(Nat.dvd_gcd_iff.mp hdvd).2, hm0⟩, (Nat.dvd_gcd_iff.mp hdvd).1⟩
    · rintro ⟨⟨hdm, _⟩, hdk⟩
      exact ⟨Nat.dvd_gcd hdk hdm, Nat.gcd_ne_zero_right hm0⟩
  rw [Finset.sum_congr rfl hstepC]
  have hstepD : ∀ k ∈ Finset.Icc 1 ⌊Z⌋₊,
      (∑ d ∈ {d ∈ m.divisors | d ∣ k}, (μ d : ℝ)) * ((1 : ℝ) / k) =
        ∑ d ∈ m.divisors, (if d ∣ k then (μ d : ℝ) * ((1 : ℝ) / k) else 0) := by
    intro k hk
    rw [Finset.sum_filter, Finset.sum_mul]
    exact Finset.sum_congr rfl fun d hd ↦ by split <;> ring
  rw [Finset.sum_congr rfl hstepD, Finset.sum_comm]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  rw [← Finset.sum_filter]
  rw [show (∑ k ∈ {k ∈ Finset.Icc 1 ⌊Z⌋₊ | d ∣ k}, (μ d : ℝ) * ((1 : ℝ) / k)) =
      (μ d : ℝ) * ∑ k ∈ {k ∈ Finset.Icc 1 ⌊Z⌋₊ | d ∣ k}, ((1 : ℝ) / k) from by
    rw [Finset.mul_sum]]
  rw [sum_one_div_filter_dvd_eq_one_div_mul_harmonicPartial d hdpos Z]
  ring

/-- Per-divisor error bound: for `m ≥ 1`, `Z ≥ 1`, and any divisor `d ∣ m`,
`|(μ(d)/d) · (harmonicPartial (Z/d) - (log (Z/d) + γ))| ≤ 5/Z`, an `O(1/Z)` bound with
absolute constant `5`. -/
theorem per_divisor_error (m : ℕ) (Z : ℝ) (hZ : 1 ≤ Z) (d : ℕ) (hd : d ∈ m.divisors) :
    |((μ d : ℝ) / d) *
        (harmonicPartial (Z / d) - (Real.log (Z / d) + Real.eulerMascheroniConstant))| ≤ 5 / Z := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have hd0 : (0 : ℝ) < (d : ℝ) := by linarith
  have hZ0 : (0 : ℝ) < Z := by linarith
  set B : ℝ := harmonicPartial (Z / d) - (Real.log (Z / d) + Real.eulerMascheroniConstant)
    with hBdef
  have hmu : |(μ d : ℝ)| ≤ 1 := by
    have : |((μ d : ℤ) : ℝ)| ≤ ((1 : ℤ) : ℝ) := by
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
    simpa using this
  have htbound : |((μ d : ℝ) / d)| ≤ 1 / d := by
    rw [abs_div, abs_of_pos hd0]; gcongr
  rw [abs_mul]
  have hγlt1 : Real.eulerMascheroniConstant < 1 := by
    have h := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' (n := 1)
    unfold Real.eulerMascheroniSeq' at h
    simp only [if_neg (by norm_num : (1 : ℕ) ≠ 0)] at h
    have : (harmonic 1 : ℝ) = 1 := by norm_num [harmonic]
    rw [this] at h
    simpa using h
  have hγpos : 0 < Real.eulerMascheroniConstant := by
    have h := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant (n := 0)
    unfold Real.eulerMascheroniSeq at h
    have hh : (harmonic 0 : ℝ) = 0 := by norm_num [harmonic]
    simp only [hh] at h
    have : Real.log ((0 : ℕ) + 1) = 0 := by norm_num
    rw [this] at h
    simpa using h
  by_cases hdZ : (d : ℝ) ≤ Z
  · have hZd1 : 1 ≤ Z / d := (one_le_div hd0).mpr hdZ
    have hBb : |B| ≤ 4 / (Z / d) := by
      rw [hBdef]; exact harmonic_bound_real (Z / d) hZd1
    have hZdpos : 0 < Z / d := by positivity
    rw [show (4 : ℝ) / (Z / d) = 4 * d / Z by field_simp] at hBb
    have hstep : |((μ d : ℝ) / d)| * |B| ≤ (1 / d) * (4 * d / Z) :=
      mul_le_mul htbound hBb (abs_nonneg _) (by positivity)
    rw [show (1 / (d : ℝ)) * (4 * d / Z) = 4 / Z by field_simp] at hstep
    have : (4 : ℝ) / Z ≤ 5 / Z := by gcongr; norm_num
    linarith
  · push Not at hdZ
    have hZdlt1 : Z / d < 1 := (div_lt_one hd0).mpr hdZ
    have hZdpos : 0 < Z / d := by positivity
    have hfloor0 : ⌊Z / d⌋₊ = 0 := Nat.floor_eq_zero.mpr hZdlt1
    have hHP0 : harmonicPartial (Z / d) = 0 := by rw [harmonicPartial, hfloor0]; simp
    have hBeq : B = -(Real.log (Z / d) + Real.eulerMascheroniConstant) := by
      rw [hBdef, hHP0]; ring
    have hlogeq : Real.log (Z / d) = Real.log Z - Real.log d := by
      rw [Real.log_div (ne_of_gt hZ0) (ne_of_gt hd0)]
    have hlogdZ : -Real.log (Z / d) = Real.log ((d : ℝ) / Z) := by
      rw [← Real.log_inv, inv_div]
    have hdZ1 : (1 : ℝ) ≤ (d : ℝ) / Z := by
      rw [le_div_iff₀ hZ0]; linarith
    have hlogle : Real.log ((d : ℝ) / Z) ≤ (d : ℝ) / Z - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have hBabs : |B| ≤ - Real.log (Z / d) + Real.eulerMascheroniConstant := by
      rw [hBeq, abs_neg]
      have hlogneg : Real.log (Z / d) < 0 := Real.log_neg hZdpos hZdlt1
      rw [abs_le]; constructor <;> linarith
    have hstep : |((μ d : ℝ) / d)| * |B| ≤
        (1 / d) * (-Real.log (Z / d) + Real.eulerMascheroniConstant) :=
      mul_le_mul htbound hBabs (abs_nonneg _) (by positivity)
    have hRHS : (1 / d) * (-Real.log (Z / d) + Real.eulerMascheroniConstant) ≤ 5 / Z := by
      rw [hlogdZ]
      have hbound1 : (1 / d) * Real.log ((d : ℝ) / Z) ≤ 1 / Z := by
        have hstep2 : (1 / d) * Real.log ((d : ℝ) / Z) ≤ (1 / d) * ((d : ℝ) / Z - 1) :=
          mul_le_mul_of_nonneg_left hlogle (by positivity)
        rw [show (1 / (d : ℝ)) * ((d : ℝ) / Z - 1) = 1 / Z - 1 / d by field_simp] at hstep2
        have : (0 : ℝ) ≤ 1 / d := by positivity
        linarith
      have hbound2 : (1 / d) * Real.eulerMascheroniConstant ≤ 1 / Z := by
        have hdd : 1 / (d : ℝ) ≤ 1 / Z := one_div_le_one_div_of_le hZ0 hdZ.le
        calc (1 / d) * Real.eulerMascheroniConstant
            ≤ (1 / Z) * 1 := mul_le_mul hdd hγlt1.le hγpos.le (by positivity)
          _ = 1 / Z := by ring
      rw [show (1 / (d : ℝ)) * (Real.log ((d : ℝ) / Z) + Real.eulerMascheroniConstant) =
        (1 / d) * Real.log ((d : ℝ) / Z) + (1 / d) * Real.eulerMascheroniConstant by ring]
      have hfin : (1 : ℝ) / Z + 1 / Z ≤ 5 / Z := by rw [← add_div]; gcongr; norm_num
      linarith
    linarith

/-- The `μ(n) log n / n` term at `n = ∏ p ∈ s, p` with `s` a finset of primes:
`(∏_{p ∈ s} (-1/p)) * (∑_{p ∈ s} log p)`. -/
theorem moebius_mul_log_div_prod_primes_eq_prod_mul_sum_log (s : Finset ℕ)
    (hall : ∀ p ∈ s, p.Prime) :
    ((μ (∏ p ∈ s, p) : ℝ) * Real.log ((∏ p ∈ s, p : ℕ) : ℝ)) / ((∏ p ∈ s, p : ℕ) : ℝ) =
      (∏ p ∈ s, (-1 / (p : ℝ))) * (∑ p ∈ s, Real.log p) := by
  have hmu : (μ (∏ p ∈ s, p) : ℝ) = ∏ p ∈ s, (-1 : ℝ) := by
    have h2 := congrArg (fun z : ℤ ↦ (z : ℝ)) (ArithmeticFunction.mu_prod_primes s hall)
    push_cast at h2
    rw [h2]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    rw [ArithmeticFunction.moebius_apply_prime (hall p hp)]
    push_cast; ring
  have hlog : Real.log (∏ p ∈ s, (p : ℝ)) = ∑ p ∈ s, Real.log p := by
    rw [Real.log_prod]
    intro p hp
    exact_mod_cast (hall p hp).pos.ne'
  have hrw : ∏ p ∈ s, (-1 / (p : ℝ)) = (∏ p ∈ s, (-1 : ℝ)) / (∏ p ∈ s, (p : ℝ)) := by
    rw [← Finset.prod_div_distrib]
  rw [hmu]
  push_cast
  rw [hlog, hrw, div_mul_eq_mul_div]

/-- For squarefree `m`, the logarithmic Möbius divisor expression equals the canonical
prime-divisor sum `ellV m`. -/
theorem divisor_log_sum_eq_ellV (m : ℕ) (hm : Squarefree m) :
    -(m / (Nat.totient m : ℝ)) * ∑ d ∈ m.divisors, ((μ d : ℝ) * Real.log d) / d = ellV m := by
  set P := m.primeFactors
  have hallP : ∀ p ∈ P, p.Prime := fun p hp ↦ Nat.prime_of_mem_primeFactors hp
  have hm0 : m ≠ 0 := hm.ne_zero
  unfold ellV
  rw [Nat.divisors_sum_powerset m hm]
  rw [show (∑ s ∈ P.powerset,
        ((μ (∏ p ∈ s, p) : ℝ) * Real.log ((∏ p ∈ s, p : ℕ) : ℝ)) /
          ((∏ p ∈ s, p : ℕ) : ℝ)) =
      ∑ s ∈ P.powerset, (∏ p ∈ s, (-1 / (p : ℝ))) * (∑ p ∈ s, Real.log p) from
    Finset.sum_congr rfl fun s hs ↦ by
      rw [Finset.mem_powerset] at hs
      exact moebius_mul_log_div_prod_primes_eq_prod_mul_sum_log s fun p hp ↦ hallP p (hs hp)]
  rw [Finset.powerset_deriv]
  have hΦ : (Nat.totient m : ℝ) / m = ∏ p ∈ P, (1 - 1 / (p : ℝ)) := by
    have h := Nat.totient_eq_mul_prod_factors m
    have hR : (Nat.totient m : ℝ) = m * ∏ p ∈ P, (1 - (p : ℝ)⁻¹) := by
      have h2 := congrArg (fun q : ℚ ↦ (q : ℝ)) h
      push_cast at h2
      convert h2 using 2
    rw [hR]
    have hm0R : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
    rw [mul_comm, mul_div_assoc, div_self hm0R, mul_one]
    exact Finset.prod_congr rfl fun p _ ↦ by rw [one_div]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun q hq ↦ ?_
  have hqprime := hallP q hq
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hqprime.pos
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hqprime.one_lt
  have hprodeq : ∏ p ∈ P.erase q, (1 + (-1 / (p : ℝ))) = ∏ p ∈ P.erase q, (1 - 1 / (p : ℝ)) :=
    Finset.prod_congr rfl fun p _ ↦ by ring
  rw [hprodeq]
  have hsplit : ∏ p ∈ P, (1 - 1 / (p : ℝ)) =
      (1 - 1 / (q : ℝ)) * ∏ p ∈ P.erase q, (1 - 1 / (p : ℝ)) := by
    rw [← Finset.prod_erase_mul P _ hq]; ring
  have hφpos : (0 : ℝ) < (Nat.totient m : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (Nat.one_le_iff_ne_zero.mpr hm0)
  have hm0R : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
  have hmφ : (m : ℝ) / (Nat.totient m : ℝ) = 1 / (∏ p ∈ P, (1 - 1 / (p : ℝ))) := by
    rw [← hΦ]; field_simp
  rw [hmφ]
  have hq1ne : (1 - 1 / (q : ℝ)) ≠ 0 := by
    have : 1 / (q : ℝ) < 1 := by rw [div_lt_one hqpos]; exact hq1
    linarith
  rw [hsplit]
  set E := ∏ p ∈ P.erase q, (1 - 1 / (p : ℝ)) with hE
  have hEpos : 0 < E := by
    rw [hE]
    refine Finset.prod_pos fun p hp ↦ ?_
    have hpp := hallP p (Finset.mem_of_mem_erase hp)
    have hlt : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    have h2 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by exact_mod_cast hpp.pos)]; exact hlt
    linarith
  have hEne : E ≠ 0 := hEpos.ne'
  field_simp

/-- **Theorem.** There is an absolute constant `C > 0` such that for every squarefree
`m ≥ 1` and every real `Z ≥ 1`, the difference between `∑_{k ≤ Z, (k,m)=1} 1/k` and the
main term `(φ(m)/m)(log Z + γ + ℓ_m)` is at most `C · τ(m)/Z` in absolute value. -/
@[pg_tag "bg246" "slem_coprime_harmonic"]
theorem coprime_reciprocal_sum_asymptotic :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → Squarefree m → ∀ Z : ℝ, 1 ≤ Z →
      |coprimeReciprocalSum m Z - (Nat.totient m / (m : ℝ)) *
            (Real.log Z + Real.eulerMascheroniConstant + ellV m)| ≤
        C * ((#m.divisors : ℝ) / Z) := by
  refine ⟨5, by norm_num, ?_⟩
  intro m hm hsf Z hZ
  rw [coprime_reindex m hm Z]
  have hkey :
      (∑ d ∈ m.divisors, ((μ d : ℝ) / d) * harmonicPartial (Z / d)) -
          (Nat.totient m / (m : ℝ)) * (Real.log Z + Real.eulerMascheroniConstant + ellV m) =
        ∑ d ∈ m.divisors, ((μ d : ℝ) / d) *
            (harmonicPartial (Z / d) - (Real.log (Z / d) + Real.eulerMascheroniConstant)) := by
    have hLC := ArithmeticFunction.sum_moebius_div_self (α := ℝ) (n := m)
    have hLC' : (Nat.totient m : ℝ) / m * ellV m = -
        ∑ d ∈ m.divisors, ((μ d : ℝ) * Real.log d) / d := by
      rw [← divisor_log_sum_eq_ellV m hsf]
      have hφ : (0 : ℝ) < (Nat.totient m : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hm
      have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
      field_simp
    rw [show (∑ d ∈ m.divisors, ((μ d : ℝ) / d) *
            (harmonicPartial (Z / d) - (Real.log (Z / d) + Real.eulerMascheroniConstant))) =
        (∑ d ∈ m.divisors, ((μ d : ℝ) / d) * harmonicPartial (Z / d)) -
          ∑ d ∈ m.divisors, ((μ d : ℝ) / d) *
              (Real.log (Z / d) + Real.eulerMascheroniConstant) from by
        rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro d hd; ring]
    have hmain : (Nat.totient m / (m : ℝ)) * (Real.log Z + Real.eulerMascheroniConstant + ellV m) =
        ∑ d ∈ m.divisors, ((μ d : ℝ) / d) *
            (Real.log (Z / d) + Real.eulerMascheroniConstant) := by
      have hexpand : ∑ d ∈ m.divisors, ((μ d : ℝ) / d) *
            (Real.log (Z / d) + Real.eulerMascheroniConstant) =
          (Real.log Z + Real.eulerMascheroniConstant) *
              (∑ d ∈ m.divisors, (μ d : ℝ) / d) -
            ∑ d ∈ m.divisors, ((μ d : ℝ) * Real.log d) / d := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun d hd ↦ ?_
        have hd0 : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
        have hZ0 : (0 : ℝ) < Z := by linarith
        rw [Real.log_div hZ0.ne' hd0.ne']
        field_simp
        ring
      rw [hexpand, hLC, mul_add, hLC']
      ring
    rw [hmain]
  rw [hkey]
  calc |∑ d ∈ m.divisors, ((μ d : ℝ) / d) *
            (harmonicPartial (Z / d) - (Real.log (Z / d) + Real.eulerMascheroniConstant))| ≤
        ∑ d ∈ m.divisors, |((μ d : ℝ) / d) *
            (harmonicPartial (Z / d) - (Real.log (Z / d) + Real.eulerMascheroniConstant))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _ ∈ m.divisors, (5 / Z) :=
          Finset.sum_le_sum fun d hd ↦ per_divisor_error m Z hZ d hd
      _ = 5 * ((#m.divisors : ℝ) / Z) := by rw [Finset.sum_const, nsmul_eq_mul]; ring

end PrimeGaps
