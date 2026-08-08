/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeHarmonic

import PrimeGapsTheory.ArithmeticFunction.Estimates
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Mertens reciprocal sums with a modulus

A Mertens estimate for reciprocal sums restricted to integers coprime to a modulus.

## Main results

* `mertens_weighted_prime_bound`: A bound for the weighted prime sum.
* `coprime_harmonic_assembly`: A formula for the coprime harmonic sum.
* `mertens_reciprocal_general`: The general-modulus Mertens reciprocal estimate.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius Finset
open Real

namespace PrimeGaps

/-- For squarefree `W`, the sum of `log p` over the prime factors equals `log W`. -/
theorem mert_sum_log_primeFactors (W : ℕ) (hWsf : Squarefree W) :
    ∑ p ∈ W.primeFactors, Real.log (p : ℝ) = Real.log (W : ℝ) := by
  rw [← Real.log_prod ?_, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hWsf]
  intro p hp
  exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne'

/-- Elementary term bound: for a prime `p` (hence `p ≥ 2`),
`log p / (p-1) ≤ 2 * log p / p`. -/
theorem mert_term_bound {p : ℕ} (hp : Nat.Prime p) :
    Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 2 * Real.log (p : ℝ) / (p : ℝ) := by
  have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
  rw [div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith [hlogp, h2p, mul_nonneg hlogp (by linarith : (0 : ℝ) ≤ (p : ℝ) - 2)]

/-- Large-prime part.  With `y := 1 + log W` (so `y = log(e·W)`), the prime factors
`p > y` contribute at most `2`. -/
theorem mert_big_bound (W : ℕ) (hWsf : Squarefree W) (hW : 1 ≤ W) :
    ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ (1 : ℝ) + Real.log (W : ℝ) < (p : ℝ)),
        Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 2 := by
  set y : ℝ := (1 : ℝ) + Real.log (W : ℝ) with hy_def
  have hlogW_nonneg : (0 : ℝ) ≤ Real.log (W : ℝ) := Real.log_nonneg (by exact_mod_cast hW)
  have hy1 : (1 : ℝ) ≤ y := by rw [hy_def]; linarith
  have hy0 : (0 : ℝ) < y := by linarith
  have hterm : ∀ p ∈ W.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)),
      Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ (2 / y) * Real.log (p : ℝ) := by
    intro p hp
    obtain ⟨hpmem, hpy⟩ := Finset.mem_filter.mp hp
    have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpmem
    have h2p : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    calc Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ 2 * Real.log (p : ℝ) / (p : ℝ) := mert_term_bound hpp
      _ ≤ 2 * Real.log (p : ℝ) / y := div_le_div_of_nonneg_left (by positivity) hy0 hpy.le
      _ = (2 / y) * Real.log (p : ℝ) := by ring
  have hnonneg : ∀ p ∈ W.primeFactors, p ∉ W.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)) →
      (0 : ℝ) ≤ Real.log (p : ℝ) := fun p hpmem _ ↦
    Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hpmem).one_lt.le)
  calc ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log (p : ℝ) / ((p : ℝ) - 1)
      ≤ ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)), (2 / y) * Real.log (p : ℝ) :=
        Finset.sum_le_sum hterm
    _ = (2 / y) * ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)), Real.log (p : ℝ) :=
        (Finset.mul_sum ..).symm
    _ ≤ (2 / y) * Real.log (W : ℝ) := by
          rw [← mert_sum_log_primeFactors W hWsf]
          exact mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) hnonneg)
            (by positivity)
    _ ≤ 2 := by
          rw [show Real.log (W : ℝ) = y - 1 by rw [hy_def]; ring, div_mul_eq_mul_div,
            div_le_iff₀ hy0]
          nlinarith [hy1]

/-- Small-prime part.  With `y := 1 + log W`, the prime factors `p ≤ y` contribute
at most `2 * log y + 2 * max Cmert 0`. -/
theorem mert_small_bound (W : ℕ) (hW : 1 ≤ W) :
    ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ (1 : ℝ) + Real.log (W : ℝ)),
        2 * Real.log (p : ℝ) / (p : ℝ) ≤
      2 * Real.log ((1 : ℝ) + Real.log (W : ℝ)) + 2 * max Cmert 0 := by
  set y : ℝ := (1 : ℝ) + Real.log (W : ℝ) with hy_def
  have hlogW_nonneg : (0 : ℝ) ≤ Real.log (W : ℝ) := Real.log_nonneg (by exact_mod_cast hW)
  have hy1 : (1 : ℝ) ≤ y := by rw [hy_def]; linarith
  have hlogy_nonneg : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
  have hcmert : (0 : ℝ) ≤ max Cmert 0 := le_max_right _ _
  by_cases hy2 : y < 2
  · have hempty : W.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp hle
      have h2p : (2 : ℝ) ≤ (p : ℝ) := by
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith
    rw [hempty, Finset.sum_empty]
    linarith only [hlogy_nonneg, hcmert]
  · push Not at hy2
    set N : ℕ := ⌊y⌋₊ with hN_def
    have hN2 : 2 ≤ N := by
      rw [hN_def]
      exact Nat.le_floor (by exact_mod_cast hy2)
    have hN1 : 1 ≤ N := one_le_two.trans hN2
    have hsub : W.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y)
          ⊆ (Finset.Icc 2 N).filter (fun p : ℕ ↦ Nat.Prime p) := by
      intro p hp
      obtain ⟨hpmem, hple⟩ := Finset.mem_filter.mp hp
      have hpp : Nat.Prime p := Nat.prime_of_mem_primeFactors hpmem
      refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hpp.two_le, ?_⟩, hpp⟩
      rw [hN_def]
      exact Nat.le_floor hple
    have hnonneg : ∀ p ∈ (Finset.Icc 2 N).filter (fun p : ℕ ↦ Nat.Prime p),
        (0 : ℝ) ≤ 2 * Real.log (p : ℝ) / (p : ℝ) := by
      intro p hp
      rw [Finset.mem_filter] at hp
      have hp0 : (0 : ℝ) ≤ (p : ℝ) := p.cast_nonneg
      have hlogp : (0 : ℝ) ≤ Real.log (p : ℝ) :=
        Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
      positivity
    have hNy : (N : ℝ) ≤ y := by
      rw [hN_def]
      exact Nat.floor_le (by linarith)
    calc ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y), 2 * Real.log (p : ℝ) / (p : ℝ)
        ≤ ∑ p ∈ (Finset.Icc 2 N).filter (fun p : ℕ ↦ Nat.Prime p),
            2 * Real.log (p : ℝ) / (p : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub fun p hp _ ↦ hnonneg p hp
      _ = 2 * ∑ p ∈ (Finset.Icc 2 N).filter (fun p : ℕ ↦ Nat.Prime p),
            Real.log (p : ℝ) / (p : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun p _ ↦ by ring
      _ ≤ 2 * (Real.log (N : ℝ) + Cmert) := by linarith only [mertens_upper N hN2]
      _ ≤ 2 * Real.log y + 2 * max Cmert 0 := by
            linarith only [Real.log_le_log (by exact_mod_cast hN1) hNy, le_max_left Cmert 0]

/-- **Weighted Mertens bound.**
There is an absolute constant `C_B > 0` such that for every squarefree `W ≥ 1`,
  `∑_{p | W} (log p)/(p-1) ≤ C_B · (1 + log log (e·W))`. -/
theorem mertens_weighted_prime_bound : ∃ C_B : ℝ, 0 < C_B ∧
      ∀ (W : ℕ), Squarefree W → 1 ≤ W → ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1) ≤
          C_B * (1 + Real.log (Real.log (rexp 1 * W))) := by
  refine ⟨4 + 2 * max Cmert 0, by positivity, ?_⟩
  intro W hWsf hW
  set y : ℝ := (1 : ℝ) + Real.log (W : ℝ) with hy_def
  have hlogW_nonneg : (0 : ℝ) ≤ Real.log (W : ℝ) := Real.log_nonneg (by exact_mod_cast hW)
  have hy1 : (1 : ℝ) ≤ y := by rw [hy_def]; linarith
  have hy_eq : y = Real.log (rexp 1 * W) := by
    rw [hy_def, Real.log_mul (by positivity) (by positivity), Real.log_exp]
  have hlogy_nonneg : (0 : ℝ) ≤ Real.log y := Real.log_nonneg hy1
  have hsplit : ∑ p ∈ W.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) =
        (∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y), Real.log (p : ℝ) / ((p : ℝ) - 1)) +
          (∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ ¬ (p : ℝ) ≤ y),
              Real.log (p : ℝ) / ((p : ℝ) - 1)) := by
    rw [Finset.sum_filter_add_sum_filter_not]
  have hsmall_term : ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y),
          Real.log (p : ℝ) / ((p : ℝ) - 1) ≤ ∑ p ∈ W.primeFactors.filter (fun p : ℕ ↦ (p : ℝ) ≤ y),
              2 * Real.log (p : ℝ) / (p : ℝ) :=
    Finset.sum_le_sum fun p hp ↦
      mert_term_bound (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp))
  have hbig_filter : W.primeFactors.filter (fun p : ℕ ↦ ¬ (p : ℝ) ≤ y) =
        W.primeFactors.filter (fun p : ℕ ↦ y < (p : ℝ)) :=
    Finset.filter_congr fun p _ ↦ by simp [not_le]
  have hA := mert_small_bound W hW
  have hB := mert_big_bound W hWsf hW
  rw [← hy_def] at hA hB
  rw [hsplit, hbig_filter, ← hy_eq]
  have hcmert : (0 : ℝ) ≤ max Cmert 0 := le_max_right _ _
  linarith only [add_le_add (hsmall_term.trans hA) hB, hlogy_nonneg, hcmert,
    mul_nonneg hcmert hlogy_nonneg]

/-- (L1) Möbius restriction: the coprime-restricted harmonic sum equals a Möbius-weighted
sum of full harmonic sums. -/
theorem asm_moebius_restriction (W : ℕ) (hW : 1 ≤ W) (N : ℕ) :
    (∑ m ∈ {m ∈ Finset.Icc 1 N | Nat.Coprime m W}, (1 : ℝ) / m) = ∑ d ∈ W.divisors,
        (μ d : ℝ) / (d : ℝ) * (harmonic (N / d) : ℝ) := by
  have moebius_sum_indicator : ∀ (n : ℕ),
      ∑ d ∈ n.divisors, (μ d : ℤ) = if n = 1 then 1 else 0 := by
    intro n
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  have hWpos : 0 < W := hW
  rw [Finset.sum_filter]
  have hsieve : ∀ m ∈ Finset.Icc 1 N, (if Nat.Coprime m W then (1 : ℝ) / m else 0) =
        ∑ d ∈ W.divisors.filter (· ∣ m), (μ d : ℝ) / m := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hm1 : 1 ≤ m := hm.1
    have hmpos : 0 < m := hm1
    have hgcd : ∑ d ∈ (Nat.gcd m W).divisors, (μ d : ℝ) =
        if Nat.gcd m W = 1 then 1 else 0 := by
      have h1 := congrArg (fun z : ℤ ↦ (z : ℝ)) (moebius_sum_indicator (Nat.gcd m W))
      push_cast at h1
      rw [h1]
    have hset : (Nat.gcd m W).divisors = W.divisors.filter (· ∣ m) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Nat.dvd_gcd_iff]
      constructor
      · rintro ⟨⟨hdm, hdW⟩, _⟩
        exact ⟨⟨hdW, by omega⟩, hdm⟩
      · rintro ⟨⟨hdW, _⟩, hdm⟩
        exact ⟨⟨hdm, hdW⟩, by simp [Nat.gcd_eq_zero_iff]; omega⟩
    by_cases hcop : Nat.Coprime m W
    · rw [if_pos hcop]
      have : Nat.gcd m W = 1 := hcop
      rw [← hset, this]
      simp only [Nat.divisors_one, Finset.sum_singleton]
      rw [ArithmeticFunction.moebius_apply_one]
      norm_num
    · rw [if_neg hcop]
      have hne : Nat.gcd m W ≠ 1 := hcop
      rw [← hset]
      rw [← Finset.sum_div, hgcd, if_neg hne]
      simp
  rw [Finset.sum_congr rfl hsieve, Finset.sum_comm' (s := Finset.Icc 1 N)
      (t := fun x ↦ W.divisors.filter (· ∣ x)) (t' := W.divisors)
      (s' := fun d ↦ (Finset.Icc 1 N).filter (d ∣ ·))
      (f := fun x d ↦ (μ d : ℝ) / x) ?_]
  · refine Finset.sum_congr rfl fun d hd ↦ ?_
    have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
    have hdr : (d : ℝ) ≠ 0 := by positivity
    have hrw : ∀ x : ℝ, (μ d : ℝ) / x = (μ d : ℝ) * (1 / x) := fun x ↦ by ring
    simp_rw [hrw, ← Finset.mul_sum]
    have hinner : ∑ i ∈ (Finset.Icc 1 N).filter (d ∣ ·), (1 : ℝ) / i =
        (1 / d) * (harmonic (N / d) : ℝ) := by
      have himg : (Finset.Icc 1 N).filter (d ∣ ·) =
          (Finset.Icc 1 (N / d)).image (fun k ↦ d * k) := by
        ext i
        simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        constructor
        · rintro ⟨⟨h1, hN⟩, k, rfl⟩
          refine ⟨k, ⟨Nat.pos_of_ne_zero fun hk ↦ by simp [hk] at h1, ?_⟩, rfl⟩
          rw [Nat.le_div_iff_mul_le hd0, Nat.mul_comm]
          omega
        · rintro ⟨k, ⟨hk1, hkN⟩, rfl⟩
          rw [Nat.le_div_iff_mul_le hd0] at hkN
          exact ⟨⟨Nat.mul_pos hd0 hk1, by rw [Nat.mul_comm]; exact hkN⟩, k, rfl⟩
      rw [himg, Finset.sum_image fun a _ b _ hab ↦ Nat.eq_of_mul_eq_mul_left hd0 hab,
        harmonic_eq_sum_Icc]
      push_cast
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk ↦ ?_
      have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
      have hkr : (k : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hinner]
    ring
  · intro x d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_Icc]
    tauto

/-- (L2) Euler-product value of the Möbius/`d` sum. -/
theorem asm_sum_moebius_div (W : ℕ) :
    ∑ d ∈ W.divisors, (μ d : ℝ) / (d : ℝ) = (W.totient : ℝ) / (W : ℝ) :=
  ArithmeticFunction.sum_moebius_div_self

/-- Euler product expansion over subsets. -/
theorem asm_Qsum (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    (∑ T ∈ S.powerset, (∏ _ ∈ T, (-1 : ℝ)) / (∏ p ∈ T, (p : ℝ))) = ∏ p ∈ S, (1 - (p : ℝ)⁻¹) := by
  induction S using Finset.induction with
  | empty => simp
  | @insert a S' ha ih =>
      have hS' : ∀ p ∈ S', 2 ≤ p := fun p hp ↦ hS p (Finset.mem_insert_of_mem hp)
      have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a S')
      have ha0 : (a : ℝ) ≠ 0 := by positivity
      rw [Finset.sum_powerset_insert ha, Finset.prod_insert ha, ih hS']
      have hsplit : ∀ t ∈ S'.powerset, (∏ p ∈ insert a t, (-1 : ℝ)) / (∏ p ∈ insert a t, (p : ℝ)) =
            (-(a : ℝ)⁻¹) * ((∏ p ∈ t, (-1 : ℝ)) / (∏ p ∈ t, (p : ℝ))) := by
        intro t ht
        have hat : a ∉ t := fun h ↦ ha (Finset.mem_powerset.mp ht h)
        have hd : (∏ p ∈ t, (p : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
          have := hS' p (Finset.mem_powerset.mp ht hp)
          positivity
        rw [Finset.prod_insert hat, Finset.prod_insert hat]
        field_simp
      rw [Finset.sum_congr rfl hsplit, ← Finset.mul_sum, ih hS']
      ring

/-- Main real-analytic induction underlying the logarithmic-derivative identity. -/
theorem asm_Lident (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) : -
    (∑ T ∈ S.powerset, (∏ _ ∈ T, (-1 : ℝ)) * (∑ p ∈ T, Real.log p) / (∏ p ∈ T, (p : ℝ))) =
      (∏ p ∈ S, (1 - (p : ℝ)⁻¹)) * ∑ q ∈ S, Real.log q / ((q : ℝ) - 1) := by
  induction S using Finset.induction with
  | empty => simp
  | @insert a S' ha ih =>
      have hS' : ∀ p ∈ S', 2 ≤ p := fun p hp ↦ hS p (Finset.mem_insert_of_mem hp)
      have ha2 : 2 ≤ a := hS a (Finset.mem_insert_self a S')
      have ha0 : (a : ℝ) ≠ 0 := by positivity
      have ha1 : (a : ℝ) - 1 ≠ 0 := by
        have h2a : (2 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha2
        intro h
        linarith
      have hsplit : ∀ t ∈ S'.powerset,
          (∏ p ∈ insert a t, (-1 : ℝ)) * (∑ p ∈ insert a t, Real.log (p : ℝ)) /
            (∏ p ∈ insert a t, (p : ℝ)) =
            (-(a : ℝ)⁻¹) * ((∏ p ∈ t, (-1 : ℝ)) * (∑ p ∈ t, Real.log (p : ℝ)) / (∏ p ∈ t,
              (p : ℝ))) +
              (-(a : ℝ)⁻¹ * Real.log (a : ℝ)) * ((∏ p ∈ t, (-1 : ℝ)) / (∏ p ∈ t, (p : ℝ))) := by
        intro t ht
        have hat : a ∉ t := fun h ↦ ha (Finset.mem_powerset.mp ht h)
        have hd : (∏ p ∈ t, (p : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun p hp ↦ by
          have := hS' p (Finset.mem_powerset.mp ht hp)
          positivity
        rw [Finset.prod_insert hat, Finset.sum_insert hat, Finset.prod_insert hat]
        field_simp
        ring
      rw [Finset.sum_powerset_insert ha, Finset.sum_congr rfl hsplit, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      have hIH := ih hS'
      have hQ := asm_Qsum S' hS'
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      set Q : ℝ := ∏ p ∈ S', (1 - (p : ℝ)⁻¹)
      set LS : ℝ := ∑ T ∈ S'.powerset,
        (∏ p ∈ T, (-1 : ℝ)) * (∑ p ∈ T, Real.log (p : ℝ)) / (∏ p ∈ T, (p : ℝ))
      set QS : ℝ := ∑ T ∈ S'.powerset, (∏ p ∈ T, (-1 : ℝ)) / (∏ p ∈ T, (p : ℝ))
      set Sig : ℝ := ∑ q ∈ S', Real.log (q : ℝ) / ((q : ℝ) - 1)
      rw [hQ, show LS = -(Q * Sig) by linarith only [hIH]]
      field_simp
      ring

/-- (L3) Logarithmic-derivative identity for the Euler product. -/
theorem asm_main_term_identity (W : ℕ) (hWsf : Squarefree W) (hW : 1 ≤ W) : -
    ∑ d ∈ W.divisors, (μ d : ℝ) * Real.log (d : ℝ) / (d : ℝ) =
      ((W.totient : ℝ) / W) * ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1) := by
  have hWne : W ≠ 0 := by omega
  set P : Finset ℕ := W.primeFactors with hP
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp ↦ (Nat.prime_of_mem_primeFactors hp).two_le
  have hfilter : W.divisors = W.divisors.filter Squarefree :=
    (Nat.divisors_filter_squarefree_of_squarefree hWsf).symm
  have hnf : (UniqueFactorizationMonoid.normalizedFactors W).toFinset = P := by
    rw [hP, Nat.factors_eq, ← Nat.toFinset_factors]
    rfl
  have hbridge : ∑ d ∈ W.divisors, (μ d : ℝ) * Real.log (d : ℝ) / (d : ℝ) =
        ∑ T ∈ P.powerset, (∏ p ∈ T, (-1 : ℝ)) * (∑ p ∈ T, Real.log (p : ℝ)) / (∏ p ∈ T,
          (p : ℝ)) := by
    rw [hfilter, Nat.sum_divisors_filter_squarefree hWne
        (f := fun d ↦ (μ d : ℝ) * Real.log (d : ℝ) / (d : ℝ)),
      hnf]
    refine Finset.sum_congr rfl fun T hT ↦ ?_
    have hTsub : T ⊆ P := Finset.mem_powerset.mp hT
    have hprod : T.val.prod = ∏ p ∈ T, p := by
      rw [Finset.prod_eq_multiset_prod]
      simp [Multiset.map_id']
    have hcop : (T : Set ℕ).Pairwise (Function.onFun Nat.Coprime id) := fun x hx y hy hxy ↦
      (Nat.coprime_primes (Nat.prime_of_mem_primeFactors (hTsub hx))
        (Nat.prime_of_mem_primeFactors (hTsub hy))).mpr hxy
    have hmu : (μ (∏ p ∈ T, p) : ℝ) = ∏ p ∈ T, (-1 : ℝ) := by
      have hmap := ArithmeticFunction.IsMultiplicative.map_prod (R := ℤ)
        (id) ArithmeticFunction.isMultiplicative_moebius T hcop
      simp only [id] at hmap
      rw [hmap]
      push_cast
      refine Finset.prod_congr rfl fun p hp ↦ ?_
      rw [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors (hTsub hp))]
      norm_num
    have hlog : Real.log ((∏ p ∈ T, p : ℕ) : ℝ) = ∑ p ∈ T, Real.log (p : ℝ) := by
      rw [Nat.cast_prod, Real.log_prod]
      exact fun p hp ↦ Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors (hTsub hp)).pos.ne'
    rw [hprod, hmu, hlog, Nat.cast_prod]
  rw [hbridge, asm_Lident P hP2, Nat.totient_div_self_eq_prod (α := ℝ) hWne, hP]

/-- Two-sided sharp bound: `|H n - log n - γ| ≤ 1/n` for `n ≥ 1`.

The Euler–Mascheroni harmonic asymptotic; a restatement (modulo
`a - (b + c) = a - b - c`) of the imported `harmonic_bound_int`. -/
theorem harmonic_sub_log_sub_gamma_abs (n : ℕ) (hn : 1 ≤ n) :
    |(harmonic n : ℝ) - Real.log n - Real.eulerMascheroniConstant| ≤ 1 / n := by
  rw [sub_sub]
  exact harmonic_bound_int n hn

/-- Nat fact: for `1 ≤ d ≤ N`, `N ≤ 2·d·⌊N/d⌋`.  Equivalently `1/⌊N/d⌋ ≤ 2d/N`. -/
theorem floor_div_mul_ge (N d : ℕ) (hd : 1 ≤ d) (hdN : d ≤ N) : N ≤ 2 * d * (N / d) := by
  have hdpos : 0 < d := hd
  have hge1 : 1 ≤ N / d := (Nat.one_le_div_iff hdpos).mpr hdN
  nlinarith [Nat.div_add_mod N d, Nat.mod_lt N hdpos, Nat.le_mul_of_pos_right d hge1]

/-- Per-divisor error after removing the main term.  For `1 ≤ d ≤ N`, the quantity
`H(⌊N/d⌋) - H(N) + log d` is `O(d/N)`: the `log d` supplies the cancellation of the
`-log d` hidden in `H(⌊N/d⌋)-H(N)`.  Uses the γ-sharp harmonic bound (γ cancels). -/
theorem abs_harmonic_div_sub_harmonic_add_log_le (N d : ℕ) (hd : 1 ≤ d) (hdN : d ≤ N) :
    |(harmonic (N / d) : ℝ) - (harmonic N : ℝ) + Real.log d| ≤ 6 * (d : ℝ) / (N : ℝ) := by
  set m : ℕ := N / d with hm_def
  have hdpos : 0 < d := hd
  have hN1 : 1 ≤ N := hd.trans hdN
  have hm1 : 1 ≤ m := by rw [hm_def]; exact (Nat.one_le_div_iff hdpos).mpr hdN
  have hD1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hDpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNrpos : (0 : ℝ) < (N : ℝ) := by linarith
  have hMr1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm1
  have hMrpos : (0 : ℝ) < (m : ℝ) := by linarith
  have hmdN : (m : ℝ) * (d : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.div_mul_le_self N d
  have hN2dm : (N : ℝ) ≤ 2 * (d : ℝ) * (m : ℝ) := by
    exact_mod_cast floor_div_mul_ge N d hd hdN
  have hNmd_eq : (N : ℝ) - (m : ℝ) * (d : ℝ) = ((N % d : ℕ) : ℝ) := by
    have hdivmod : (N : ℝ) = (d : ℝ) * (m : ℝ) + ((N % d : ℕ) : ℝ) := by
      exact_mod_cast (Nat.div_add_mod N d).symm
    linarith
  have hNmd_lt : (N : ℝ) - (m : ℝ) * (d : ℝ) < (d : ℝ) := by
    rw [hNmd_eq]
    exact_mod_cast Nat.mod_lt N hdpos
  have hHN := harmonic_sub_log_sub_gamma_abs N hN1
  have hHm := harmonic_sub_log_sub_gamma_abs m hm1
  set γ : ℝ := Real.eulerMascheroniConstant
  rw [abs_le] at hHN hHm
  have hmdpos : (0 : ℝ) < (m : ℝ) * (d : ℝ) := by positivity
  have hδ_eq : Real.log (m : ℝ) - Real.log (N : ℝ) + Real.log (d : ℝ) =
      Real.log ((m : ℝ) * (d : ℝ) / (N : ℝ)) := by
    rw [Real.log_div hmdpos.ne' hNrpos.ne', Real.log_mul hMrpos.ne' hDpos.ne']
    ring
  have hδ_nonpos : Real.log ((m : ℝ) * (d : ℝ) / (N : ℝ)) ≤ 0 := by
    refine Real.log_nonpos (by positivity) ?_
    rw [div_le_one hNrpos]
    exact hmdN
  have hmd_ge : (N : ℝ) / 2 ≤ (m : ℝ) * (d : ℝ) := by linarith only [hN2dm]
  have hratio : (N : ℝ) / ((m : ℝ) * (d : ℝ)) - 1 ≤ 2 * (d : ℝ) / (N : ℝ) := by
    rw [show (N : ℝ) / ((m : ℝ) * (d : ℝ)) - 1 =
        ((N : ℝ) - (m : ℝ) * (d : ℝ)) / ((m : ℝ) * (d : ℝ)) by field_simp,
      div_le_div_iff₀ hmdpos hNrpos]
    linarith only [mul_le_mul_of_nonneg_right hNmd_lt.le hNrpos.le,
      mul_le_mul_of_nonneg_left hmd_ge (by linarith only [hDpos] : (0 : ℝ) ≤ 2 * (d : ℝ))]
  have hδ_abs : |Real.log ((m : ℝ) * (d : ℝ) / (N : ℝ))| ≤ 2 * (d : ℝ) / (N : ℝ) := by
    rw [abs_of_nonpos hδ_nonpos]
    calc -Real.log ((m : ℝ) * (d : ℝ) / (N : ℝ))
        = Real.log ((N : ℝ) / ((m : ℝ) * (d : ℝ))) := by rw [← Real.log_inv, inv_div]
      _ ≤ (N : ℝ) / ((m : ℝ) * (d : ℝ)) - 1 := Real.log_le_sub_one_of_pos (by positivity)
      _ ≤ 2 * (d : ℝ) / (N : ℝ) := hratio
  have hinvm : 1 / (m : ℝ) ≤ 2 * (d : ℝ) / (N : ℝ) := by
    rw [div_le_div_iff₀ hMrpos hNrpos]
    linarith only [hN2dm]
  have hinvN : 1 / (N : ℝ) ≤ 2 * (d : ℝ) / (N : ℝ) := by
    rw [div_le_div_iff₀ hNrpos hNrpos]
    linarith only [mul_nonneg hNrpos.le (by linarith only [hD1] : (0 : ℝ) ≤ 2 * (d : ℝ) - 1)]
  have hkey : (harmonic m : ℝ) - (harmonic N : ℝ) + Real.log (d : ℝ) =
      Real.log ((m : ℝ) * (d : ℝ) / (N : ℝ)) + (((harmonic m : ℝ) - Real.log (m : ℝ) - γ) -
          ((harmonic N : ℝ) - Real.log (N : ℝ) - γ)) := by
    rw [← hδ_eq]
    ring
  have key6 : (2 : ℝ) * (d : ℝ) / (N : ℝ) + 2 * (d : ℝ) / (N : ℝ) + 2 * (d : ℝ) / (N : ℝ) =
      6 * (d : ℝ) / (N : ℝ) := by
    ring
  rw [hkey, abs_le]
  have hδval := abs_le.mp hδ_abs
  constructor
  · linarith only [hδval.1, hHm.1, hHN.2, hinvm, hinvN, key6]
  · linarith only [hδval.2, hHm.2, hHN.1, hinvm, hinvN, key6]

/-- The real cast of the Möbius function is bounded by `1` in absolute value. -/
private lemma abs_moebius_cast_le_one (d : ℕ) : |(μ d : ℝ)| ≤ 1 := by
  rw [← Int.cast_abs]
  exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- Large-divisor term bound: for `d > N = ⌊x⌋₊` (so `d > x`), `H(⌊N/d⌋)=0` and the
term `μ(d)/d·(H(⌊N/d⌋) - log(x/d))` has absolute value `≤ 1/x`. -/
theorem large_d_term_bound (x : ℝ) (hx : 1 ≤ x) (d : ℕ) (hd : ⌊x⌋₊ < d) :
    |(μ d : ℝ) / (d : ℝ) *
        ((harmonic (⌊x⌋₊ / d) : ℝ) - Real.log (x / d))| ≤ 1 / x := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hd1 : 1 ≤ d := le_trans (Nat.le_floor (by exact_mod_cast hx : ((1 : ℕ) : ℝ) ≤ x)) hd.le
  have hdr1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hdx : x < (d : ℝ) := by
    have h1 : x < (⌊x⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one x
    have h3 : ((⌊x⌋₊ : ℝ) + 1) ≤ (d : ℝ) := by exact_mod_cast hd
    linarith
  rw [Nat.div_eq_of_lt hd]
  simp only [harmonic_zero, Rat.cast_zero, zero_sub]
  rw [abs_mul, abs_div, abs_of_pos hdpos]
  have hmu := abs_moebius_cast_le_one d
  have hfrac_le : |(μ d : ℝ)| / (d : ℝ) ≤ 1 / (d : ℝ) := by gcongr
  have hlog_neg : Real.log (x / (d : ℝ)) ≤ 0 := by
    refine Real.log_nonpos (by positivity) ?_
    rw [div_le_one hdpos]
    linarith
  rw [show |(-Real.log (x / (d : ℝ)))| = Real.log ((d : ℝ) / x) by
    rw [abs_neg, abs_of_nonpos hlog_neg, ← Real.log_inv, inv_div]]
  have hlog_nonneg : (0 : ℝ) ≤ Real.log ((d : ℝ) / x) := by
    refine Real.log_nonneg ?_
    rw [le_div_iff₀ hxpos]
    linarith
  calc |(μ d : ℝ)| / (d : ℝ) * Real.log ((d : ℝ) / x)
      ≤ 1 / (d : ℝ) * Real.log ((d : ℝ) / x) := mul_le_mul_of_nonneg_right hfrac_le hlog_nonneg
    _ ≤ 1 / (d : ℝ) * ((d : ℝ) / x - 1) :=
        mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (by positivity)) (by positivity)
    _ = 1 / x - 1 / (d : ℝ) := by field_simp
    _ ≤ 1 / x := sub_le_self _ (by positivity)

private lemma abs_sum_le_card_divisors_mul {W : ℕ} {S : Finset ℕ} (hS : S ⊆ W.divisors)
    {g : ℕ → ℝ} {c : ℝ} (hc : 0 ≤ c) (hterm : ∀ d ∈ S, |g d| ≤ c) :
    |∑ d ∈ S, g d| ≤ (#W.divisors : ℝ) * c :=
  calc |∑ d ∈ S, g d| ≤ ∑ d ∈ S, |g d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ S, c := Finset.sum_le_sum hterm
    _ = (#S : ℝ) * c := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (#W.divisors : ℝ) * c :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_le_card hS) hc

private lemma abs_sum_moebius_harmonic_shift_le (W N : ℕ) (hN1 : 1 ≤ N) :
    |∑ d ∈ {d ∈ W.divisors | d ≤ N}, (μ d : ℝ) / (d : ℝ) *
          ((harmonic (N / d) : ℝ) - (harmonic N : ℝ) + Real.log (d : ℝ))| ≤
      6 * ((#W.divisors : ℝ) / (N : ℝ)) := by
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hterm : ∀ d ∈ {d ∈ W.divisors | d ≤ N},
      |(μ d : ℝ) / (d : ℝ) *
        ((harmonic (N / d) : ℝ) - (harmonic N : ℝ) + Real.log (d : ℝ))| ≤ 6 / (N : ℝ) := by
    intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    have hdpos : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hd.1)
    have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
    rw [abs_mul]
    have hmufrac : |(μ d : ℝ) / (d : ℝ)| ≤ 1 / (d : ℝ) := by
      rw [abs_div, abs_of_pos hdr]
      have hmu := abs_moebius_cast_le_one d
      gcongr
    calc |(μ d : ℝ) / (d : ℝ)| *
          |(harmonic (N / d) : ℝ) - (harmonic N : ℝ) + Real.log (d : ℝ)| ≤
        (1 / (d : ℝ)) * (6 * (d : ℝ) / (N : ℝ)) :=
          mul_le_mul hmufrac (abs_harmonic_div_sub_harmonic_add_log_le N d hdpos hd.2)
            (abs_nonneg _) (by positivity)
      _ = 6 / (N : ℝ) := by field_simp
  calc |∑ d ∈ {d ∈ W.divisors | d ≤ N}, (μ d : ℝ) / (d : ℝ) *
            ((harmonic (N / d) : ℝ) - (harmonic N : ℝ) + Real.log (d : ℝ))| ≤
      (#W.divisors : ℝ) * (6 / (N : ℝ)) :=
        abs_sum_le_card_divisors_mul (Finset.filter_subset _ _) (by positivity) hterm
    _ = 6 * ((#W.divisors : ℝ) / (N : ℝ)) := by ring

/-- `0 < φ(W)` as a real, for `W ≥ 1`. -/
private lemma totient_pos_real {W : ℕ} (hW : 1 ≤ W) : (0 : ℝ) < (W.totient : ℝ) := by
  exact_mod_cast Nat.totient_pos.mpr hW

/-- `1 ≤ τ(W)` as a real, for `W ≥ 1`, since `1` divides `W`. -/
private lemma one_le_card_divisors_real {W : ℕ} (hW : 1 ≤ W) :
    (1 : ℝ) ≤ (#W.divisors : ℝ) := by
  have : 1 ≤ #W.divisors :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  exact_mod_cast this

private lemma abs_sum_moebius_div_filter_le (W N : ℕ) (hW : 1 ≤ W) (hN1 : 1 ≤ N)
    (hτN : (#W.divisors : ℝ) / (N : ℝ) ≤ 2 * ((W.totient : ℝ) / (W : ℝ))) :
    |∑ d ∈ {d ∈ W.divisors | d ≤ N},
        (μ d : ℝ) / (d : ℝ)| ≤ 3 * ((W.totient : ℝ) / (W : ℝ)) := by
  set τ : ℝ := (#W.divisors : ℝ) with hτ_def
  set q : ℝ := (W.totient : ℝ) / (W : ℝ) with hq_def
  have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hφpos : (0 : ℝ) < (W.totient : ℝ) := totient_pos_real hW
  have hq_pos : (0 : ℝ) < q := by rw [hq_def]; positivity
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hL2 : ∑ d ∈ W.divisors, (μ d : ℝ) / (d : ℝ) = q := by
    rw [hq_def]; exact asm_sum_moebius_div W
  have hsplit2 : ∑ d ∈ W.divisors, (μ d : ℝ) / (d : ℝ) =
      (∑ d ∈ {d ∈ W.divisors | d ≤ N}, (μ d : ℝ) / (d : ℝ)) +
        (∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N}, (μ d : ℝ) / (d : ℝ)) :=
    (Finset.sum_filter_add_sum_filter_not W.divisors (fun d ↦ d ≤ N) _).symm
  have htail : |∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N},
      (μ d : ℝ) / (d : ℝ)| ≤ 2 * q := by
    have htail_term : ∀ d ∈ {d ∈ W.divisors | ¬ d ≤ N},
        |(μ d : ℝ) / (d : ℝ)| ≤ 1 / (N : ℝ) := by
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hd.1)
      have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      rw [abs_div, abs_of_pos hdr]
      have hmu := abs_moebius_cast_le_one d
      have hNd : (N : ℝ) ≤ (d : ℝ) := by exact_mod_cast (not_le.mp hd.2).le
      calc |(μ d : ℝ)| / (d : ℝ) ≤ 1 / (d : ℝ) := by gcongr
        _ ≤ 1 / (N : ℝ) := div_le_div_of_nonneg_left (by norm_num) (by linarith) hNd
    calc |∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N},
            (μ d : ℝ) / (d : ℝ)| ≤ τ * (1 / (N : ℝ)) := by
          rw [hτ_def]
          exact abs_sum_le_card_divisors_mul (Finset.filter_subset _ _) (by positivity) htail_term
      _ = τ / (N : ℝ) := by ring
      _ ≤ 2 * q := hτN
  have heq : ∑ d ∈ {d ∈ W.divisors | d ≤ N}, (μ d : ℝ) / (d : ℝ) =
      q - ∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N},
          (μ d : ℝ) / (d : ℝ) := by
    rw [← hL2, hsplit2]; ring
  rw [heq]
  calc |q - ∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N}, (μ d : ℝ) / (d : ℝ)|
      ≤ |q| + |∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N},
          (μ d : ℝ) / (d : ℝ)| := abs_sub _ _
    _ ≤ q + 2 * q := by
          rw [abs_of_pos hq_pos]
          linarith only [htail]
    _ = 3 * q := by ring

/-- (L4) **Analytic kernel.** The Möbius-weighted harmonic sum is within `O(φ/W)` of the
Möbius-weighted logarithm `M = ∑_{d|W} μ(d)/d · log(x/d)`. Uses `x ≥ W τ(W)/φ(W)`. -/
theorem asm_harmonic_error : ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), Squarefree W → 1 ≤ W →
        ∀ (x : ℝ), x ≥ (W : ℝ) * (#W.divisors : ℝ) / (W.totient : ℝ) →
          |(∑ d ∈ W.divisors,
              (μ d : ℝ) / (d : ℝ) * (harmonic (⌊x⌋₊ / d) : ℝ)) -
              ∑ d ∈ W.divisors, (μ d : ℝ) / (d : ℝ) * Real.log (x / d)| ≤
            C * ((W.totient : ℝ) / W) := by
  refine ⟨25, by norm_num, ?_⟩
  intro W hWsf hW x hx
  set N : ℕ := ⌊x⌋₊ with hN_def
  set τ : ℝ := (#W.divisors : ℝ) with hτ_def
  set q : ℝ := (W.totient : ℝ) / (W : ℝ) with hq_def
  have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
  have hφpos : (0 : ℝ) < (W.totient : ℝ) := totient_pos_real hW
  have hq_pos : (0 : ℝ) < q := by rw [hq_def]; positivity
  have hτ1 : (1 : ℝ) ≤ τ := by rw [hτ_def]; exact one_le_card_divisors_real hW
  have hφle : (W.totient : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.totient_le W
  have hx1 : (1 : ℝ) ≤ x := by
    have h1 : (1 : ℝ) ≤ (W : ℝ) * τ / (W.totient : ℝ) := by
      rw [le_div_iff₀ hφpos]
      linarith only [hφle, le_mul_of_one_le_right (by linarith only [hWr] : (0 : ℝ) ≤ (W : ℝ)) hτ1]
    rw [hτ_def] at h1; linarith only [hx, h1]
  have hxpos : (0 : ℝ) < x := by linarith
  have hN1 : 1 ≤ N := by rw [hN_def]; exact Nat.le_floor (by exact_mod_cast hx1)
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hNx : (N : ℝ) ≤ x := by rw [hN_def]; exact Nat.floor_le hxpos.le
  have hxN1 : x < (N : ℝ) + 1 := by rw [hN_def]; exact_mod_cast Nat.lt_floor_add_one x
  have hτx : τ / x ≤ q := by
    have hx' : (W : ℝ) * τ ≤ x * (W.totient : ℝ) := (div_le_iff₀ hφpos).mp hx
    rw [hq_def, div_le_div_iff₀ hxpos (by positivity)]
    linarith only [hx']
  have hτN : τ / (N : ℝ) ≤ 2 * q := by
    have h2N : x ≤ 2 * (N : ℝ) := by
      rcases le_or_gt 2 x with hx2 | hx2
      · linarith [hxN1]
      · have hN : N = 1 := by
          rw [hN_def, Nat.floor_eq_iff hxpos.le]
          exact ⟨by exact_mod_cast hx1, by push_cast; linarith⟩
        rw [hN]
        push_cast
        linarith
    calc τ / (N : ℝ) ≤ τ / (x / 2) :=
          div_le_div_of_nonneg_left (by linarith only [hτ1]) (by positivity) (by linarith)
      _ = 2 * (τ / x) := by ring
      _ ≤ 2 * q := by linarith only [hτx]
  have hHNlogx : |(harmonic N : ℝ) - Real.log x| ≤ 3 := by
    have hHN := harmonic_sub_log_sub_gamma_abs N hN1
    rw [abs_le] at hHN
    have hγlb : (1 : ℝ) / 2 < Real.eulerMascheroniConstant :=
      Real.one_half_lt_eulerMascheroniConstant
    have hγub : Real.eulerMascheroniConstant < 2 / 3 := Real.eulerMascheroniConstant_lt_two_thirds
    have hinvN : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact hNr1
    have hlogxN_nonneg : Real.log (N : ℝ) ≤ Real.log x := Real.log_le_log (by linarith) hNx
    have hlogxN_ub : Real.log x - Real.log (N : ℝ) ≤ 1 / (N : ℝ) := by
      rw [show Real.log x - Real.log (N : ℝ) = Real.log (x / (N : ℝ)) by
        rw [Real.log_div (by linarith) (by linarith)]]
      refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
      rw [div_sub_one (by linarith), div_le_div_iff₀ (by linarith) (by linarith)]
      linarith only [mul_le_mul_of_nonneg_right
        (by linarith only [hxN1] : x - (N : ℝ) ≤ 1) (by linarith only [hNr1] : (0 : ℝ) ≤ (N : ℝ))]
    rw [abs_le]
    constructor <;> linarith [hHN.1, hHN.2, hinvN, hlogxN_nonneg, hlogxN_ub]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_filter_add_sum_filter_not W.divisors (fun d ↦ d ≤ N)]
  set f : ℕ → ℝ := fun d ↦ (μ d : ℝ) / (d : ℝ) * (harmonic (N / d) : ℝ) -
      (μ d : ℝ) / (d : ℝ) * Real.log (x / d) with hf_def
  have hbig : |∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N}, f d| ≤ q := by
    have hterm : ∀ d ∈ {d ∈ W.divisors | ¬ d ≤ N}, |f d| ≤ 1 / x := by
      intro d hd
      rw [Finset.mem_filter] at hd
      have hdN : N < d := by omega
      have heq : f d = (μ d : ℝ) / (d : ℝ) *
          ((harmonic (⌊x⌋₊ / d) : ℝ) - Real.log (x / d)) := by
        rw [← hN_def]
        simp only [hf_def]
        ring
      rw [heq]
      exact large_d_term_bound x hx1 d (by rw [← hN_def]; exact hdN)
    calc |∑ d ∈ {d ∈ W.divisors | ¬ d ≤ N}, f d| ≤ τ * (1 / x) := by
          rw [hτ_def]
          exact abs_sum_le_card_divisors_mul (Finset.filter_subset _ _) (by positivity) hterm
      _ = τ / x := by ring
      _ ≤ q := hτx
  have hsmall : |∑ d ∈ {d ∈ W.divisors | d ≤ N}, f d| ≤ 24 * q := by
    have hf_rw : ∀ d ∈ {d ∈ W.divisors | d ≤ N},
        f d = (μ d : ℝ) / (d : ℝ) *
                ((harmonic (N / d) : ℝ) - (harmonic N : ℝ) + Real.log (d : ℝ)) +
              (μ d : ℝ) / (d : ℝ) * ((harmonic N : ℝ) - Real.log x) := by
      intro d hd
      rw [Finset.mem_filter, Nat.mem_divisors] at hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors (Nat.mem_divisors.mpr hd.1)
      have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
      have hlogxd : Real.log (x / d) = Real.log x - Real.log (d : ℝ) := by
        rw [Real.log_div (by linarith) hdr.ne']
      simp only [hf_def, hlogxd]
      ring
    rw [Finset.sum_congr rfl hf_rw, Finset.sum_add_distrib]
    set A : ℝ := ∑ d ∈ {d ∈ W.divisors | d ≤ N},
        (μ d : ℝ) / (d : ℝ) *
          ((harmonic (N / d) : ℝ) - (harmonic N : ℝ) + Real.log (d : ℝ)) with hA_def
    set B : ℝ := ∑ d ∈ {d ∈ W.divisors | d ≤ N},
        (μ d : ℝ) / (d : ℝ) * ((harmonic N : ℝ) - Real.log x) with hB_def
    have hA : |A| ≤ 12 * q := by
      calc |A| ≤ 6 * (τ / (N : ℝ)) := by
            rw [hA_def, hτ_def]
            exact abs_sum_moebius_harmonic_shift_le W N hN1
        _ ≤ 6 * (2 * q) := mul_le_mul_of_nonneg_left hτN (by norm_num)
        _ = 12 * q := by ring
    have hB : |B| ≤ 12 * q := by
      have hpartial : |∑ d ∈ {d ∈ W.divisors | d ≤ N},
          (μ d : ℝ) / (d : ℝ)| ≤ 3 * q := by
        rw [hq_def]
        exact abs_sum_moebius_div_filter_le W N hW hN1 (by rw [← hq_def, ← hτ_def]; exact hτN)
      rw [hB_def, ← Finset.sum_mul, abs_mul]
      calc |∑ d ∈ {d ∈ W.divisors | d ≤ N},
              (μ d : ℝ) / (d : ℝ)| * |(harmonic N : ℝ) - Real.log x| ≤
          (3 * q) * 3 := mul_le_mul hpartial hHNlogx (abs_nonneg _) (by positivity)
        _ = 9 * q := by ring
        _ ≤ 12 * q := by linarith only [hq_pos]
    exact (abs_add_le A B).trans (by linarith only [hA, hB])
  exact (abs_add_le _ _).trans (by linarith only [hsmall, hbig])

/-- **Assembly of the main estimate.**
For an absolute constant `C_A > 0`, every squarefree `W ≥ 1` and every
`x ≥ W·τ(W)/φ(W)` satisfy
`|S(x,W) - (φ(W)/W)·log x| ≤ C_A·(φ(W)/W)·(1 + ∑_{p|W} log p/(p-1))`,
where `S(x,W)` is the coprime-restricted reciprocal sum.  Combines the Möbius
restriction (`asm_moebius_restriction`, L1), the Euler-product value
`∑_{d|W} μ(d)/d = φ(W)/W` (`asm_sum_moebius_div`, L2), the logarithmic-derivative
identity (`asm_main_term_identity`, L3) and the analytic error bound
(`asm_harmonic_error`, L4). -/
theorem coprime_harmonic_assembly : ∃ C_A : ℝ, 0 < C_A ∧ ∀ (W : ℕ), Squarefree W → 1 ≤ W →
        ∀ (x : ℝ), x ≥ (W : ℝ) * (#W.divisors : ℝ) / (W.totient : ℝ) →
          |(∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime m W}, (1 : ℝ) / m) -
              (W.totient : ℝ) / W * Real.log x| ≤ C_A * ((W.totient : ℝ) / W) *
                (1 + ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1)) := by
  obtain ⟨C, hCpos, hC⟩ := asm_harmonic_error
  refine ⟨C + 1, by positivity, ?_⟩
  intro W hWsf hW x hx
  set N : ℕ := ⌊x⌋₊ with hN_def
  have hg_pos : (0 : ℝ) < (W.totient : ℝ) / W := by
    have hφ : (0 : ℝ) < (W.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hW
    have hWr : (0 : ℝ) < (W : ℝ) := by exact_mod_cast hW
    positivity
  set S : ℝ := ∑ m ∈ {m ∈ Finset.Icc 1 N | Nat.Coprime m W}, (1 : ℝ) / m with hS
  set MH : ℝ := ∑ d ∈ W.divisors,
    (μ d : ℝ) / (d : ℝ) * (harmonic (N / d) : ℝ) with hMH
  set M : ℝ := ∑ d ∈ W.divisors,
    (μ d : ℝ) / (d : ℝ) * Real.log (x / d) with hM
  have hL1 : S = MH := asm_moebius_restriction W hW N
  have hL4 : |MH - M| ≤ C * ((W.totient : ℝ) / W) := hC W hWsf hW x hx
  have hxge1 : (1 : ℝ) ≤ x := by
    have hWr : (1 : ℝ) ≤ (W : ℝ) := by exact_mod_cast hW
    have hτ1 : (1 : ℝ) ≤ (#W.divisors : ℝ) := one_le_card_divisors_real hW
    have hφpos : (0 : ℝ) < (W.totient : ℝ) := totient_pos_real hW
    have hφle : (W.totient : ℝ) ≤ (W : ℝ) := by exact_mod_cast Nat.totient_le W
    have h1 : (1 : ℝ) ≤ (W : ℝ) * (#W.divisors : ℝ) / (W.totient : ℝ) := by
      rw [le_div_iff₀ hφpos]
      linarith only [hφle,
        le_mul_of_one_le_right (by linarith only [hWr] : (0 : ℝ) ≤ (W : ℝ)) hτ1]
    linarith only [hx, h1]
  have hxpos : (0 : ℝ) < x := by linarith
  have hMsplit : M = (W.totient : ℝ) / W * Real.log x +
      ((W.totient : ℝ) / W) * ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1) := by
    have hlog_split : ∀ d ∈ W.divisors,
        (μ d : ℝ) / (d : ℝ) * Real.log (x / d) =
        (μ d : ℝ) / (d : ℝ) * Real.log x -
          (μ d : ℝ) * Real.log (d : ℝ) / (d : ℝ) := by
      intro d hd
      have hdr : (0 : ℝ) < (d : ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors hd
      rw [Real.log_div hxpos.ne' hdr.ne']
      ring
    have hL2 := asm_sum_moebius_div W
    have hL3 := asm_main_term_identity W hWsf hW
    rw [hM, Finset.sum_congr rfl hlog_split, Finset.sum_sub_distrib, ← Finset.sum_mul, hL2, ← hL3]
    ring
  have hkey : S - (W.totient : ℝ) / W * Real.log x =
      (MH - M) + ((W.totient : ℝ) / W) * ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1) := by
    rw [hL1, hMsplit]
    ring
  have hPnn : (0 : ℝ) ≤ ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1) := by
    refine Finset.sum_nonneg fun p hp ↦ ?_
    have h2p : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    exact div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
  calc |S - (W.totient : ℝ) / W * Real.log x|
      = |(MH - M) + ((W.totient : ℝ) / W) * ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1)| := by
        rw [hkey]
    _ ≤ |MH - M| + |((W.totient : ℝ) / W) * ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1)| :=
        abs_add_le _ _
    _ ≤ C * ((W.totient : ℝ) / W) +
          ((W.totient : ℝ) / W) * ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1) := by
        gcongr
        rw [abs_of_nonneg (by positivity)]
    _ ≤ (C + 1) * ((W.totient : ℝ) / W) *
          (1 + ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1)) := by
        linarith only [hg_pos.le, mul_nonneg (mul_nonneg hCpos.le hg_pos.le) hPnn]

/-- `log (log (e · x))` is nonnegative as soon as `1 ≤ x`, because then
`log (e · x) ≥ log e = 1`. -/
theorem log_log_exp_one_mul_nonneg {x : ℝ} (hx : 1 ≤ x) :
    (0 : ℝ) ≤ Real.log (Real.log (rexp 1 * x)) := by
  refine Real.log_nonneg ?_
  calc (1 : ℝ) = Real.log (rexp 1) := (Real.log_exp 1).symm
    _ ≤ Real.log (rexp 1 * x) :=
        Real.log_le_log (Real.exp_pos 1) (le_mul_of_one_le_right (Real.exp_pos 1).le hx)

/-- **General-modulus Mertens reciprocal sum.**
There is an absolute constant `C > 0` such that for every squarefree `W ≥ 1` and
every `x ≥ W·τ(W)/φ(W)`,
`|∑_{m ≤ x, (m,W)=1} 1/m - (φ(W)/W)·log x| ≤ C·(φ(W)/W)·(1 + log log (e·W))`.
Obtained by combining `coprime_harmonic_assembly` with the weighted Mertens bound
`mertens_weighted_prime_bound`. -/
@[pg_tag "bg246" "lem_mertens_reciprocal_W"]
theorem mertens_reciprocal_general : ∃ C : ℝ, 0 < C ∧ ∀ (W : ℕ), Squarefree W → 1 ≤ W →
        ∀ (x : ℝ), x ≥ (W : ℝ) * (#W.divisors : ℝ) / (W.totient : ℝ) →
          |(∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime m W}, (1 : ℝ) / m) -
              (W.totient : ℝ) / W * Real.log x| ≤ C * ((W.totient : ℝ) / W) *
                (1 + Real.log (Real.log (rexp 1 * W))) := by
  obtain ⟨C_A, hC_A, hA⟩ := coprime_harmonic_assembly
  obtain ⟨C_B, hC_B, hB⟩ := mertens_weighted_prime_bound
  refine ⟨C_A * (1 + C_B), by positivity, ?_⟩
  intro W hWsf hW x hx
  have hg_pos : (0 : ℝ) < (W.totient : ℝ) / W := by
    have hWpos : 0 < W := hW
    have hφ : 0 < W.totient := Nat.totient_pos.mpr hWpos
    positivity
  have hloglog_nonneg : (0 : ℝ) ≤ Real.log (Real.log (rexp 1 * W)) :=
    log_log_exp_one_mul_nonneg (by exact_mod_cast hW)
  have hg : (0 : ℝ) ≤ (W.totient : ℝ) / W := hg_pos.le
  calc
    |(∑ m ∈ {m ∈ Finset.Icc 1 ⌊x⌋₊ | Nat.Coprime m W}, (1 : ℝ) / m) -
        (W.totient : ℝ) / W * Real.log x| ≤ C_A * ((W.totient : ℝ) / W) *
            (1 + ∑ p ∈ W.primeFactors, Real.log p / ((p : ℝ) - 1)) := hA W hWsf hW x hx
    _ ≤ C_A * (1 + C_B) * ((W.totient : ℝ) / W) * (1 + Real.log (Real.log (rexp 1 * W))) := by
          linarith only [mul_le_mul_of_nonneg_left (hB W hWsf hW) (mul_nonneg hC_A.le hg),
            mul_nonneg (mul_nonneg hC_A.le hg) hloglog_nonneg]

end PrimeGaps
