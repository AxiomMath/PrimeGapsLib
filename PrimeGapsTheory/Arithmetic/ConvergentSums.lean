/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Tactic.NormNum.Prime
public import PrimeGapsTheory.Arithmetic.Totient.Basic

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Convergent arithmetic sums

Convergence of Möbius-weighted series involving the functions `g` and `φ`.

## Main definitions

* `term`: The odd-supported summand involving `μ` and `g`.
* `F`: The summable dominating sequence `n ↦ 1/(n-2)²` used to bound `term` on primes.

## Main results

* `convergent_sum_g`: The Möbius-weighted series involving `g` converges.
* `lem_convergent_sum_phi`: The analogous series involving `φ` converges.
-/

@[expose] public section

open ArithmeticFunction
open scoped ArithmeticFunction.detotient

open Real
open scoped ArithmeticFunction.Moebius ArithmeticFunction.sigma ArithmeticFunction.zeta Finset

namespace PrimeGaps

/-- The summand of the series, viewed as a function `ℕ → ℝ`. It is `0` on even
arguments (matching the restriction `gcd(s, 2) = 1`) and `μ(s)² / g(s)²` on odd
arguments, where positivity of `g` makes the denominator nonzero. -/
noncomputable def term (s : ℕ) : ℝ :=
  if Odd s then ((μ s : ℝ)) ^ 2 / (g s : ℝ) ^ 2 else 0

/-- `term 1 = 1`. -/
theorem term_one : term 1 = 1 := by simp [term]

/-- Every term is nonnegative (it is either a square-over-square or `0`). -/
theorem term_nonneg (m : ℕ) : 0 ≤ term m := by unfold term; split <;> positivity

/-- The odd-support presentation of `term` is equal to its squarefree-support presentation.
For an even squarefree number, the latter vanishes because `g 2 = 0`; for a nonsquarefree
number, both presentations vanish because its Möbius value is zero. -/
theorem term_eq_squarefree (n : ℕ) : term n = if (1 ≤ n ∧ Squarefree n) then
      |(μ n : ℝ)| / (g n : ℝ) ^ 2 else 0 := by
  classical
  unfold term
  by_cases hodd : Odd n
  · rw [if_pos hodd]
    by_cases hsf : Squarefree n
    · have hsq : (μ n : ℝ) ^ 2 = 1 :=
        mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      rw [if_pos ⟨hodd.pos, hsf⟩, hsq, ← Real.sqrt_sq_eq_abs, hsq, Real.sqrt_one]
    · rw [if_neg fun h ↦ hsf h.2, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp
  · rw [if_neg hodd]
    by_cases hguard : 1 ≤ n ∧ Squarefree n
    · rw [if_pos hguard]
      obtain ⟨t, rfl⟩ := (Nat.not_odd_iff_even.mp hodd).two_dvd
      rw [ArithmeticFunction.isMultiplicative_detotient.map_mul_of_coprime
        (Nat.squarefree_mul_iff.mp hguard.2).1]
      simp [ArithmeticFunction.detotient_prime Nat.prime_two]
    · rw [if_neg hguard]

/-- `term` is multiplicative across coprime arguments. -/
theorem term_coprime_mul {m n : ℕ} (h : m.Coprime n) : term (m * n) = term m * term n := by
  rcases eq_or_ne m 0 with rfl | -
  · simp [term, (Nat.coprime_zero_left _).mp h]
  rcases eq_or_ne n 0 with rfl | -
  · simp [term, (Nat.coprime_zero_right _).mp h]
  unfold term
  by_cases hmn : Odd (m * n)
  · obtain ⟨hom, hon⟩ := Nat.odd_mul.mp hmn
    have hmu : (μ (m * n) : ℝ) = (μ m : ℝ) * (μ n : ℝ) :=
      mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime h
    have hg : (g (m * n) : ℝ) = (g m : ℝ) * (g n : ℝ) :=
      mod_cast ArithmeticFunction.isMultiplicative_detotient.map_mul_of_coprime h
    rw [if_pos hmn, if_pos hom, if_pos hon, hmu, hg]
    ring
  · rw [if_neg hmn]
    rw [Nat.odd_mul] at hmn
    push Not at hmn
    by_cases hom : Odd m
    · rw [if_neg (hmn hom)]; ring
    · rw [if_neg hom]; ring

/-- For a prime `p` and exponent `k ≥ 2`, `term (p^k) = 0`: `p^k` is not
squarefree, so `μ(p^k) = 0`. -/
theorem term_prime_pow_zero {p : ℕ} (hp : Nat.Prime p) {k : ℕ} (hk : 2 ≤ k) : term (p ^ k) = 0 := by
  unfold term
  have hsq : ¬ Squarefree (p ^ k) := by
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]; push Not; intro; omega
  split <;> simp [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]

/-- For each prime `p`, the sequence `k ↦ ‖term (p^k)‖` is summable: it is
supported on `{0, 1}` (higher prime powers are not squarefree, so vanish). -/
theorem term_prime_pow_summable {p : ℕ} (hp : Nat.Prime p) : Summable (fun k ↦ ‖term (p ^ k)‖) := by
  refine summable_of_ne_finset_zero (s := {0, 1}) fun k hk ↦ ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  rw [term_prime_pow_zero hp (by omega), norm_zero]

/-- For each prime `p`, the per-prime tsum collapses: `∑'_k term(p^k) = 1 + term p`.
Powers `p^k` with `k ≥ 2` vanish (`term_prime_pow_zero`) and `term 1 = 1`
(`term_one`), so the only surviving terms are at `k = 0` and `k = 1`. -/
theorem term_tsum_prime {p : ℕ} (hp : Nat.Prime p) : ∑' (k : ℕ), term (p ^ k) = 1 + term p := by
  rw [tsum_eq_sum (s := {0, 1})]
  · simp [term_one]
  · intro k hk
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
    exact term_prime_pow_zero hp (by omega)

/-- The dominating sequence `F n = 1/(n-2)²` for `n ≥ 3` (and `0` otherwise).
It bounds `term p` from above on primes and is summable (shifted Basel series). -/
noncomputable def F : ℕ → ℝ := fun n ↦ if 3 ≤ n then 1 / ((n : ℝ) - 2) ^ 2 else 0

/-- `F` is nonnegative. -/
theorem F_nonneg (n : ℕ) : 0 ≤ F n := by unfold F; split <;> positivity

/-- `F` is summable: reindexing `n ↦ n + 3` turns it into the shifted Basel
series `∑ 1/(m+1)²`, which converges (`Real.summable_one_div_nat_pow`). -/
theorem F_summable : Summable F := by
  rw [← summable_nat_add_iff 3]
  have hbasel : Summable (fun m : ℕ ↦ 1 / ((m : ℝ) + 1) ^ 2) := by
    simpa using (summable_nat_add_iff 1).mpr
      (Real.summable_one_div_nat_pow.mpr (by norm_num : (1 : ℕ) < 2))
  refine hbasel.congr fun n ↦ ?_
  simp only [F]
  rw [if_pos (Nat.le_add_left 3 n)]
  congr 1
  push_cast
  ring

/-- On a prime `p`, `term p = F p`. For odd primes `p ≥ 3`, `term p = 1/(p-2)²`
(since `μ(p)² = 1` and `g p = p - 2`); for `p = 2`, both sides are `0`. -/
theorem term_prime_eq {p : ℕ} (hp : Nat.Prime p) : term p = F p := by
  unfold term F
  by_cases hodd : Odd p
  · have hp3 : 3 ≤ p := by
      have := hp.two_le
      have := Nat.odd_iff.mp hodd
      omega
    have hmu : (μ p : ℝ) ^ 2 = 1 := by
      rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
    have hg : (g p : ℝ) = (p : ℝ) - 2 := by
      rw [ArithmeticFunction.detotient_prime hp, Nat.cast_sub hp.two_le]
      norm_num
    rw [if_pos hodd, if_pos hp3, hmu, hg]
  · obtain rfl : p = 2 := hp.eq_two_or_odd'.resolve_right hodd
    rw [if_neg hodd, if_neg (by omega)]

/-- **Analytic kernel (Euler-product convergence).** The partial Euler products
of `term`, namely `∏_{p < N} (∑'_k term(p^k))`, are uniformly bounded by
`rexp (∑' n, F n)`, independently of `N`. -/
theorem term_euler_prod_bounded :
    ∃ B : ℝ, ∀ N : ℕ, (∏ p ∈ N.primesBelow, ∑' (k : ℕ), term (p ^ k)) ≤ B := by
  refine ⟨rexp (∑' n, F n), fun N ↦ ?_⟩
  have hsumbd : (∑ p ∈ N.primesBelow, term p) ≤ ∑' n, F n :=
    (Finset.sum_congr rfl fun p hp ↦ term_prime_eq (Nat.prime_of_mem_primesBelow hp)).trans_le
      (F_summable.sum_le_tsum N.primesBelow fun i _ ↦ F_nonneg i)
  calc (∏ p ∈ N.primesBelow, ∑' (k : ℕ), term (p ^ k))
      = ∏ p ∈ N.primesBelow, (1 + term p) :=
        Finset.prod_congr rfl fun p hp ↦ term_tsum_prime (Nat.prime_of_mem_primesBelow hp)
    _ ≤ ∏ p ∈ N.primesBelow, rexp (term p) :=
        Finset.prod_le_prod (fun p _ ↦ by linarith [term_nonneg p])
          (fun p _ ↦ by rw [add_comm]; exact Real.add_one_le_exp (term p))
    _ = rexp (∑ p ∈ N.primesBelow, term p) := (Real.exp_sum N.primesBelow term).symm
    _ ≤ rexp (∑' n, F n) := Real.exp_le_exp.mpr hsumbd

/-- The series `∑_{s ≥ 1, (s,2)=1} μ(s)² / g(s)²` converges: the family
of nonnegative terms `term` is summable. Proved via the Euler-product summability
lemma `EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum` together
with the uniform bound `term_euler_prod_bounded`. -/
@[pg_tag "bg246" "lem_convergent_sum_g"]
theorem convergent_sum_g : Summable term := by
  classical
  obtain ⟨B, hB⟩ := term_euler_prod_bounded
  apply summable_of_sum_range_le term_nonneg (c := B)
  intro n
  have hsum : HasSum (fun m : n.smoothNumbers ↦ term m)
      (∏ p ∈ n.primesBelow, ∑' (k : ℕ), term (p ^ k)) :=
    (EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_tsum
      term_one (fun {m n} ↦ term_coprime_mul) (fun {p} ↦ term_prime_pow_summable) n).2
  have hsub : ∀ i ∈ Finset.range n, term i ≠ 0 → i ∈ n.smoothNumbers := by
    intro i hi hne
    rw [Finset.mem_range] at hi
    refine Nat.mem_smoothNumbers.mpr ⟨fun h ↦ hne (by simp [term, h]), fun p hp ↦ ?_⟩
    have := Nat.le_of_mem_primeFactorsList hp
    omega
  calc ∑ i ∈ Finset.range n, term i
      = ∑ x ∈ (Finset.range n).subtype (· ∈ n.smoothNumbers), term (x : ℕ) := by
        rw [Finset.sum_subtype_eq_sum_filter, Finset.sum_filter_of_ne hsub]
    _ ≤ ∏ p ∈ n.primesBelow, ∑' (k : ℕ), term (p ^ k) :=
        sum_le_hasSum _ (fun i _ ↦ term_nonneg _) hsum
    _ ≤ B := hB n

/-- The summand `μ(s)² / φ(s)²` is nonnegative: a ratio of two squares
(Mathlib's `0/0 = 0` convention keeps this true even when `φ(s) = 0`). -/
lemma summand_nonneg (s : ℕ) :
    0 ≤ ((μ s : ℝ)) ^ 2 / ((Nat.totient s : ℝ)) ^ 2 := by positivity

end PrimeGaps

namespace Nat

/-- The number of divisors of `n` is at most `2 √n`. -/
lemma card_divisors_le_two_mul_sqrt (n : ℕ) : #n.divisors ≤ 2 * n.sqrt := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  set s := n.sqrt with hs
  rw [← Finset.filter_union_filter_not_eq (p := fun d ↦ d ≤ s) n.divisors]
  refine (Finset.card_union_le _ _).trans ?_
  have hsmall : #{d ∈ n.divisors | d ≤ s} ≤ s := by
    refine (Finset.card_le_card (?_ : _ ⊆ Finset.Icc 1 s)).trans (by simp)
    intro d hd
    rw [Finset.mem_filter] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd.1, hd.2⟩
  have hlarge : #{d ∈ n.divisors | ¬ d ≤ s} ≤ #{d ∈ n.divisors | d ≤ s} := by
    refine Finset.card_le_card_of_injOn (fun d ↦ n / d) (fun d hd ↦ ?_) (fun a ha b hb hab ↦ ?_)
    · rw [Finset.mem_coe, Finset.mem_filter] at hd ⊢
      obtain ⟨hdmem, hds⟩ := hd
      push Not at hds
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdmem
      refine ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hdvd, hn⟩, ?_⟩
      by_contra! hcon
      have hmul : (s + 1) * (s + 1) ≤ d * (n / d) := Nat.mul_le_mul hds hcon
      rw [Nat.mul_div_cancel' hdvd] at hmul
      have hlt : n < (s + 1) * (s + 1) := by
        simpa [hs, pow_two] using Nat.lt_succ_sqrt n
      omega
    · rw [Finset.mem_coe, Finset.mem_filter] at ha hb
      simp only at hab
      have : n / (n / a) = n / (n / b) := by rw [hab]
      rwa [Nat.div_div_self (Nat.dvd_of_mem_divisors ha.1) hn,
        Nat.div_div_self (Nat.dvd_of_mem_divisors hb.1) hn] at this
  omega

/-- Real-valued form: `d(n)^2 ≤ 4 n`. -/
lemma card_divisors_sq_le_four_mul (n : ℕ) : (#n.divisors : ℝ) ^ 2 ≤ 4 * n := by
  have hnat : #n.divisors ^ 2 ≤ 4 * n :=
    calc #n.divisors ^ 2
        ≤ (2 * n.sqrt) ^ 2 := Nat.pow_le_pow_left (card_divisors_le_two_mul_sqrt n) 2
      _ = 4 * (n.sqrt * n.sqrt) := by ring
      _ ≤ 4 * n := by have := Nat.sqrt_le n; omega
  exact_mod_cast hnat

end Nat

namespace ArithmeticFunction

/-- The majorant series `∑ d(n)/n^{3/2}` is summable.
Since `d = σ₀ = ζ ⋆ ζ` (Dirichlet convolution) and `ζ` is `L`-summable for
`Re s > 1`, the convolution `ζ * ζ` is `L`-summable at every real `s > 1`; transferring
the complex `LSeriesSummable` statement to the real norm gives summability of
`d(n)/n^s`. -/
lemma summable_sigma_zero_div_rpow {s : ℝ} (hs : 1 < s) :
    Summable (fun n : ℕ ↦ ((σ 0 n : ℕ) : ℝ) / (n : ℝ) ^ s) := by
  have hLS : LSeriesSummable (fun n ↦ ((σ 0 n : ℕ) : ℂ)) (s : ℂ) := by
    have hzC : LSeriesSummable
        (fun n ↦ ((↑(ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) n)) (s : ℂ) := by
      have hh : LSeriesSummable (fun n ↦ (ζ n : ℂ)) (s : ℂ) := by
        rw [LSeriesSummable_zeta_iff]; simpa using hs
      convert hh using 2 with n; norm_cast
    have hmul := LSeriesSummable_mul hzC hzC
    have hcoe : ((↑(ζ : ArithmeticFunction ℕ) : ArithmeticFunction ℂ) *
        (↑(ζ : ArithmeticFunction ℕ))) = ↑(σ 0 : ArithmeticFunction ℕ) := by
      rw [← ArithmeticFunction.zeta_mul_pow_eq_sigma, ArithmeticFunction.pow_zero_eq_zeta]
      push_cast; ring
    rw [hcoe] at hmul
    convert hmul using 2 with n; norm_cast
  rw [LSeriesSummable] at hLS
  refine hLS.norm.congr fun n ↦ ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [LSeries.term]
  rw [LSeries.term_def]
  simp only [hn, if_false]
  rw [norm_div, Complex.norm_natCast]
  congr 1
  rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast Nat.pos_of_ne_zero hn)]
  simp

end ArithmeticFunction

namespace PrimeGaps

/-- Pointwise majorant: `μ(s)^2/φ(s)^2 ≤ 2 · d(s)/s^{3/2}`.
From `s ≤ φ(s)·d(s)` we get `1/φ(s)^2 ≤ d(s)^2/s^2`; from `μ(s)^2 ≤ 1` then
`μ(s)^2/φ(s)^2 ≤ d(s)^2/s^2`; finally `d(s) ≤ 2√s` upgrades `d(s)^2/s^2` to
`2 d(s)/s^{3/2}`. -/
lemma moebius_sq_div_totient_sq_le (s : ℕ) :
    ((μ s : ℝ)) ^ 2 / ((Nat.totient s : ℝ)) ^ 2 ≤
      2 * ((σ 0 s : ℕ) : ℝ) / (s : ℝ) ^ (3 / 2 : ℝ) := by
  rw [sigma_zero_apply]
  rcases eq_or_ne s 0 with rfl | hs0
  · norm_num
  have hs : 1 ≤ s := Nat.one_le_iff_ne_zero.mpr hs0
  have hA : (s : ℝ) ≤ (Nat.totient s : ℝ) * (#s.divisors : ℝ) :=
    mod_cast Nat.le_totient_mul_card_divisors s
  have hB : (#s.divisors : ℝ) ^ 2 ≤ 4 * s := Nat.card_divisors_sq_le_four_mul s
  have hM : ((μ s : ℝ)) ^ 2 ≤ 1 := by
    rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
    split_ifs <;> norm_num
  set D : ℝ := (#s.divisors : ℝ) with hD
  set F : ℝ := (Nat.totient s : ℝ) with hF
  set M : ℝ := (μ s : ℝ) with hMdef
  set r : ℝ := Real.sqrt s with hr
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hFpos : (0 : ℝ) < F := by rw [hF]; exact_mod_cast Nat.totient_pos.mpr hs
  have hDpos : (0 : ℝ) ≤ D := by rw [hD]; positivity
  have hrpos : (0 : ℝ) < r := Real.sqrt_pos.mpr hsR
  have hrsq : r ^ 2 = (s : ℝ) := Real.sq_sqrt hsR.le
  have h32 : (s : ℝ) ^ (3 / 2 : ℝ) = (s : ℝ) * r := by
    rw [hr, Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
      Real.rpow_add hsR, Real.rpow_one]
  have hDle : D ≤ 2 * r := by nlinarith [hB, hrpos, hDpos, hrsq]
  rw [h32]
  have step1 : M ^ 2 / F ^ 2 ≤ D ^ 2 / (s : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hA, hM, hFpos, hDpos, hsR, mul_pos hFpos hFpos]
  have step2 : D ^ 2 / (s : ℝ) ^ 2 ≤ 2 * D / ((s : ℝ) * r) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity), ← hrsq]
    have key : 0 ≤ D * r ^ 3 * (2 * r - D) :=
      mul_nonneg (mul_nonneg hDpos (pow_pos hrpos 3).le) (by linarith)
    nlinarith [key]
  exact le_trans step1 step2

/-- A uniform bound `C` on every finite partial sum `∑_{s ∈ u} μ(s)² / φ(s)²`, obtained from the
summable majorant `2 * d(s) / s^(3/2)`. -/
lemma partial_sum_le : ∃ C : ℝ, ∀ u : Finset ℕ,
      ∑ s ∈ u, ((μ s : ℝ)) ^ 2 / ((Nat.totient s : ℝ)) ^ 2 ≤ C := by
  set M : ℕ → ℝ := fun s ↦ 2 * ((σ 0 s : ℕ) : ℝ) / (s : ℝ) ^ (3 / 2 : ℝ) with hMdef
  have hMsum : Summable M :=
    ((ArithmeticFunction.summable_sigma_zero_div_rpow
      (by norm_num : (1 : ℝ) < 3 / 2)).mul_left 2).congr fun n ↦ by simp only [hMdef]; ring
  have hMnonneg : ∀ s, 0 ≤ M s := fun s ↦ by simp only [hMdef]; positivity
  exact ⟨∑' s, M s, fun u ↦ (Finset.sum_le_sum fun s _ ↦ moebius_sq_div_totient_sq_le s).trans
    (hMsum.sum_le_tsum u fun i _ ↦ hMnonneg i)⟩

/-- The series `∑_{s ≥ 1} μ(s)² / φ(s)²` converges, where `φ` is Euler's totient.
The nonnegative summand is dominated by `2 · d(s) / s^{3/2}` (`moebius_sq_div_totient_sq_le`),
whose summability (`ArithmeticFunction.summable_sigma_zero_div_rpow`) gives a uniform bound on
all finite partial sums (`partial_sum_le`), whence `summable_of_sum_le`. -/
@[pg_tag "bg246" "lem_convergent_sum_phi"]
theorem lem_convergent_sum_phi :
    Summable (fun s : ℕ ↦ ((μ s : ℝ)) ^ 2 / ((Nat.totient s : ℝ)) ^ 2) :=
  partial_sum_le.elim fun _ hC ↦ summable_of_sum_le summand_nonneg hC

end PrimeGaps
