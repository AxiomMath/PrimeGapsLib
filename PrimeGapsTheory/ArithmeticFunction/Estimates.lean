/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.ArithmeticFunction.Rpow
public import PrimeGapsTheory.ArithmeticFunction.Tau
public import PrimeGapsTheory.ArithmeticFunction.Totient

import Mathlib.Analysis.Complex.ExponentialBounds
import PrimeGapsTheory.Analysis.SpecificSums
import PrimeGapsTheory.Analysis.Zeta
import PrimeGapsTheory.ArithmeticFunction.Basic
import PrimeGapsTheory.ForMathlib.Algebra.Order.Field.Basic
import PrimeGapsTheory.ForMathlib.Analysis.SpecialFunctions.Log.Summable
import PrimeGapsTheory.ForMathlib.NumberTheory.ArithmeticFunction.Moebius
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Estimates of arithmetic functions

Bounds and summability results for the divisor functions `τ k`, the Euler totient `φ` and the
Möbius function `μ`, together with the Euler products and Mertens-type sums built from them.

## Main results

* `Nat.div_totient_le_const_mul_rpow`: `n / φ n` is bounded by `C * n ^ ε` for every `ε > 0`.
* `ArithmeticFunction.sum_moebius_div_self`: `∑ d ∣ n, μ d / d = φ n / n`.
* `ArithmeticFunction.sum_moebius_sq_div_totient`: `∑ e ∣ n, μ e ^ 2 / φ e = n / φ n`.
* `ArithmeticFunction.sum_moebius_sq_mul_tau_div_totient_le` and
  `ArithmeticFunction.prod_mul_sum_one_div_prod_totient_le`: Mertens-type bounds for the sums of
  `τ k` weighted by `1 / φ`, in one and in several variables.
-/

@[expose] public section

open Finset Real Complex
open ArithmeticFunction zeta Moebius Nat

namespace Nat

@[pg_tag "bg246" "lem_euler_product_mu_over_d"]
theorem totient_div_self_eq_prod {α : Type*} [Field α] [CharZero α]
    {n : ℕ} (hn : n ≠ 0) : (φ n / n : α) = ∏ p ∈ n.primeFactors, (1 - (p : α)⁻¹) := by
  simpa [div_eq_iff (Nat.cast_ne_zero.mpr hn : (n : α) ≠ 0), mul_comm] using
    congrArg (Rat.cast (K := α)) (totient_eq_mul_prod_factors n)

theorem div_totient_eq_prod {α : Type*} [Field α] [CharZero α]
    {n : ℕ} (hn : n ≠ 0) : (n / φ n : α) = ∏ p ∈ n.primeFactors, (1 - (p : α)⁻¹)⁻¹ := by
  simp [← totient_div_self_eq_prod hn]

/-- This is a significant over-estimate. The true upper-asymptote is `e^γ log log n`. -/
theorem div_totient_le_const_mul_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ C, ∀ n : ℕ, (n / φ n : ℝ) ≤ C * n ^ ε := by
  let x₀ := max 2 ((2 : ℝ) ^ ε⁻¹)
  have hx₀ {x : ℝ} (hx : x₀ ≤ x) : (1 - x⁻¹)⁻¹ ≤ x ^ ε := by
    nth_grw 1 [← (le_max_left _ _).trans hx, ← (le_max_right _ _).trans hx]
    norm_num [← rpow_mul, inv_mul_cancel₀ hε.ne']
  refine ⟨∏ p ∈ primesBelow ⌈x₀⌉₊, (1 - (p : ℝ)⁻¹)⁻¹, fun n ↦ ?_⟩
  obtain rfl | hn := eq_or_ne n 0
  · simp [hε.ne']
  rw [div_totient_eq_prod hn, ← prod_filter_mul_prod_filter_not _ (· < ⌈x₀⌉₊)]
  have hp₀ {p : ℕ} (hp : p.Prime) : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (mod_cast hp.one_lt)
  have hp₁ {p : ℕ} (hp : p.Prime) : 1 ≤ (1 - (p : ℝ)⁻¹)⁻¹ :=
    one_le_one_sub_inv_inv (mod_cast hp.one_lt)
  refine mul_le_mul ?_ ?_ (prod_nonneg <| by simp_all [(hp₀ _).le])
    (prod_nonneg <| by simp_all [mem_primesBelow, (hp₀ _).le])
  · exact prod_le_prod_of_subset_of_one_le (by simp +contextual [subset_iff, mem_primesBelow])
      (by grind) (by simp_all [mem_primesBelow])
  · grw [Finset.prod_le_prod (g := fun n : ℕ ↦ (n : ℝ) ^ ε) (by simp_all [(hp₀ _).le])
      (by simp_all), prod_le_prod_of_subset_of_one_le (filter_subset _ _) (by simp [rpow_nonneg])
      fun p hp _ ↦ one_le_rpow (by simp_all [Prime.one_le]) hε.le, finsetProd_rpow _ _ (by simp),
      ← cast_prod, le_of_dvd (by positivity) n.prod_primeFactors_dvd]

theorem injOn_mul_dvd_product_squarefree {d : ℕ} :
    Set.InjOn (fun p ↦ p.1 * p.2) ({e | e ∣ d} ×ˢ {s | Squarefree (d * s)}) := by
  rintro ⟨e₁, s₁⟩ ⟨he₁, hs₁⟩ ⟨e₂, s₂⟩ ⟨he₂, hs₂⟩ heq
  simp only [squarefree_mul_iff, Prod.mk.injEq] at *
  obtain rfl : e₁ = e₂ := by
    rw [← gcd_eq_left he₁, ← hs₁.1.symm.gcd_mul_right_cancel, heq,
      hs₂.1.symm.gcd_mul_right_cancel, gcd_eq_left he₂]
  exact ⟨rfl, mul_left_cancel₀ (ne_zero_of_dvd_ne_zero hs₁.2.1.ne_zero he₁) heq⟩

end Nat

section summability

theorem hasSum_tau_div_rpow {r : ℕ} {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n ↦ (τ r n : ℝ) / n ^ σ) (riemannZeta σ ^ r).re := by
  convert hasSum_re <| LSeriesHasSum_tau_riemannZeta_pow (s := σ) (by simpa) with n
  rw [LSeries.term_def₀ (by simp), ← ofReal_natCast (τ r n), ← ofReal_natCast n, ← ofReal_neg,
    ← ofReal_cpow n.cast_nonneg, ← ofReal_mul, ofReal_re, rpow_neg n.cast_nonneg, div_eq_mul_inv]

theorem summable_tau_div_totient_mul_rpow {r : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    Summable fun n ↦ (τ r n : ℝ) / (φ n * n ^ σ) := by
  obtain ⟨C, hC⟩ := div_totient_le_const_mul_rpow <| half_pos hσ
  refine Summable.of_nonneg_of_le (fun _ ↦ by positivity) (fun n ↦ ?_)
    ((hasSum_tau_div_rpow (r := r) (σ := 1 + σ / 2) (by simpa)).summable.mul_left C)
  obtain rfl | hn := eq_or_ne n 0
  · simp
  grw [div_mul_eq_div_div, ← div_mul_div_cancel₀ (a := (τ r n : ℝ))
    (by positivity : (n : ℝ) ≠ 0), hC]
  simp only [show 1 + σ / 2 = 1 + -(σ / 2) + σ by ring,
    rpow_add (by positivity : 0 < (n : ℝ)), rpow_one, rpow_neg n.cast_nonneg]
  exact le_of_eq <| by field_simp

theorem lseriesSummable_tau_div_totient {r : ℕ} {s : ℂ} (hσ : 0 < s.re) :
    LSeriesSummable (fun n ↦ τ r n / φ n) s := by
  rw [LSeriesSummable_iff_of_re_eq_re (s' := s.re) (by norm_cast), LSeriesSummable,
    ← summable_norm_iff]
  convert summable_tau_div_totient_mul_rpow (r := r) hσ with n
  rw [LSeries.term_def₀ (by simp), norm_mul, norm_natCast_cpow_of_re_ne_zero n (by aesop)]
  simp [rpow_neg, div_eq_mul_inv, mul_assoc, mul_comm]

theorem summable_moebius_sq_mul_tau_div_totient_mul_rpow {r : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    Summable fun n ↦ (μ n ^ 2 * τ r n : ℝ) / (φ n * n ^ σ) :=
  (summable_tau_div_totient_mul_rpow (r := r) hσ).of_nonneg_of_le (fun _ ↦ by positivity) fun n ↦
    div_le_div_of_nonneg_right (mul_le_of_le_one_left (by positivity)
      (mod_cast (sq_le_one_iff_abs_le_one (μ n)).mpr abs_moebius_le_one)) (by positivity)

theorem lseriesSummable_moebius_sq_mul_tau_div_totient {r : ℕ} {s : ℂ} (hσ : 0 < s.re) :
    LSeriesSummable (fun n ↦ μ n ^ 2 * τ r n / φ n) s := by
  refine (summable_norm_iff.mpr <| lseriesSummable_tau_div_totient (r := r) hσ).of_norm_bounded
    fun n ↦ LSeries.norm_term_le s ?_
  rw [← Int.cast_pow, moebius_sq]
  split_ifs <;> simp [div_nonneg]

end summability

namespace ArithmeticFunction

@[pg_tag "bg246" "lem_euler_product_mu_over_d"]
theorem sum_moebius_div_self {α : Type*} [Field α] [CharZero α] {n : ℕ} :
    ∑ d ∈ n.divisors, (μ d / d : α) = φ n / n := by
  obtain rfl | hn := eq_or_ne n 0
  · simp
  rw [eq_div_iff_mul_eq (by positivity), sum_mul]
  simp_rw [div_mul_eq_mul_div₀, mul_div_assoc]
  trans ((∑ x ∈ n.divisorsAntidiagonal, μ x.1 * ArithmeticFunction.id x.2 : ℤ) : α)
  · rw [sum_divisorsAntidiagonal (μ · * ArithmeticFunction.id ·), Int.cast_sum]
    exact sum_congr rfl fun x hx ↦ by aesop
  simp_rw [← natCoe_apply, ← mul_apply, ← zeta_mul_totient, natCoe_mul, ← mul_assoc]
  simp

@[pg_tag "bg246" "lem_phi_lower_sf"]
theorem le_tau₂_mul_totient {n : ℕ} : n ≤ τ₂ n * φ n := by
  rw [pow_two, mul_zeta_apply, sum_mul]
  nth_rw 1 [← sum_totient n]
  refine sum_le_sum fun d hd ↦ ?_
  obtain ⟨hdvd, hn⟩ := mem_divisors.mp hd
  rw [zeta_apply_ne (ne_zero_of_dvd_ne_zero hn hdvd), one_mul]
  exact le_of_dvd (totient_pos.mpr (pos_of_ne_zero hn)) (totient_dvd_of_dvd hdvd)

@[pg_tag "bg246" "lem_phi_lower_sf"]
theorem div_tau₂_le_totient {α : Type*} [Field α] [CharZero α] [LinearOrder α]
    [IsStrictOrderedRing α] {n : ℕ} : (n / τ₂ n : α) ≤ φ n :=
  div_le_of_le_mul₀ (τ₂ n).cast_nonneg (φ n).cast_nonneg <|
    mod_cast le_tau₂_mul_totient.trans_eq (mul_comm ..)

@[pg_tag "bg246" "lem_n_over_phi_expansion"]
theorem sum_moebius_sq_div_totient {α : Type*} [Field α] [CharZero α] {n : ℕ} :
    ∑ e ∈ n.divisors, (μ e ^ 2 / φ e : α) = n / φ n := by
  suffices (((μ : ArithmeticFunction ℚ).ppow 2).pdiv totient * ζ : ArithmeticFunction ℚ) =
      ArithmeticFunction.id.pdiv totient by
    simpa [-mul_apply, coe_mul_zeta_apply] using congr(($this n : α))
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (by aesop) _ (by aesop)).mpr
    fun p n hp ↦ ?_
  suffices ∑ e ∈ (p ^ n).divisors, (μ e ^ 2 / φ e : ℚ) = p ^ n / φ (p ^ n) by
    simpa [-mul_apply, coe_mul_zeta_apply]
  obtain _ | n := n
  · simp
  rw [totient_prime_pow_succ hp, pow_succ (p : ℚ), cast_mul, cast_pow,
    mul_div_mul_left _ _ (by simp [hp.ne_zero]), sum_divisors_prime_pow hp, sum_range_succ',
    sum_range_succ', sum_eq_zero fun i _ ↦ by simp [moebius_apply_prime_pow hp]]
  simp [hp, totient_prime, moebius_apply_prime, hp.one_le]
  grind [Nat.Prime.one_lt, Nat.one_lt_cast]

@[pg_tag "bg246" "lem_n_over_phi_expansion"]
theorem sum_squarefree_totient_inv {α : Type*} [Field α] [CharZero α] {n : ℕ} :
    ∑ e ∈ n.divisors with Squarefree e, (φ e : α)⁻¹ = n / φ n := by
  simp [sum_filter_squarefree, ← div_eq_mul_inv, sum_moebius_sq_div_totient]

@[pg_tag "bg246" "lem_n_over_phi_expansion"]
theorem sum_totient_inv {α : Type*} [Field α] [CharZero α] {n : ℕ} (hn : Squarefree n) :
    ∑ e ∈ n.divisors, (φ e : α)⁻¹ = n / φ n :=
  Nat.divisors_filter_squarefree_of_squarefree hn ▸ sum_squarefree_totient_inv

theorem eulerProduct_moebius_sq_mul_tau_div_totient_mul_rpow {r : ℕ} {σ : ℝ} (hσ : 0 < σ) :
    HasProd (fun p : Primes ↦ (1 + r / ((p - 1) * p ^ σ) : ℝ))
      (∑' n : ℕ, (μ n ^ 2 * τ r n : ℝ) / (φ n * n ^ σ)) := by
  set f : ArithmeticFunction ℝ :=
    (((μ : ArithmeticFunction ℝ).ppow 2).pmul (τ r)).pdiv (.pmul totient (.rpow σ))
  have h (n : ℕ) : (μ n ^ 2 * τ r n : ℝ) / (φ n * n ^ σ) = f n := by simp [f, hσ.ne']
  rw [tsum_congr h]
  refine (IsMultiplicative.eulerProduct_hasProd (by aesop) ?_).congr_fun fun p ↦ ?_
  · simpa [f, hσ.ne', abs_rpow_of_nonneg] using summable_moebius_sq_mul_tau_div_totient_mul_rpow hσ
  · rw [tsum_eq_sum (s := range 2) fun n hn ↦ ?_]
    · simp [f, sum_range_succ, p.2, hσ.ne', totient_prime, Nat.cast_sub p.2.one_le,
        moebius_apply_prime]
    · simp [f, moebius_apply_prime_pow p.2, show n ≠ 0 ∧ n ≠ 1 by grind]

theorem summable_prime_one_div_sub_one_mul_rpow {σ : ℝ} (hσ : 0 < σ) :
    Summable fun p : Primes ↦ (1 / ((p - 1) * p ^ σ) : ℝ) :=
  ((summable_tau_div_totient_mul_rpow (r := 1) hσ).subtype Nat.Prime).congr fun p ↦ by
    simp [p.2.ne_zero, totient_prime p.2, p.2.one_le]

theorem tsum_one_div_sub_one_mul_rpow_le {σ : ℝ} (hσ : 0 < σ) :
    ∑' p : Primes, (1 / ((p - 1) * p ^ σ) : ℝ) ≤ (1 + σ).log - σ.log + 1 := by
  have h₁ {n : ℕ} (hn : 2 ≤ n) :
      (1 / ((n - 1) * n ^ σ) : ℝ) = 1 / n ^ (1 + σ) + 1 / (n * (n - 1) * n ^ σ) := by
    have h : (1 : ℝ) < n := mod_cast hn
    rw [rpow_add (one_pos.trans h), rpow_one]
    field_simp [sub_ne_zero.mpr h.ne']
    ring
  rw [tsum_congr fun p ↦ h₁ p.2.two_le]
  have h₂ (p : Primes) : (0 : ℝ) < p * (p - 1) :=
    mul_pos (by simp [p.2.pos]) (by simp [p.2.one_lt])
  have h₃ (p : Primes) : (1 / (p * (p - 1) * p ^ σ) : ℝ) ≤ 1 / (p * (p - 1)) :=
    one_div_le_one_div_of_le (h₂ p) <|
      le_mul_of_one_le_right (h₂ p).le <| one_le_rpow (by simp [p.2.one_le]) hσ.le
  have h₄ : Summable fun p : Primes ↦ (1 / (p * (p - 1) * p ^ σ) : ℝ) :=
    (hasSum_one_div_mul_sub_one.summable.subtype Nat.Prime).of_nonneg_of_le
      (fun p ↦ one_div_nonneg.mpr <| mul_nonneg (h₂ p).le <| rpow_nonneg p.1.cast_nonneg _) h₃
  have h₅ : ∑' p : Primes, (1 / (p * (p - 1) * p ^ σ) : ℝ) ≤ 1 := by
    refine (h₄.tsum_le_tsum_of_inj (g := fun n : ℕ ↦ (1 / (n * (n - 1)) : ℝ)) _
      Subtype.val_injective (fun n _ ↦ ?_) h₃
      hasSum_one_div_mul_sub_one.summable).trans_eq hasSum_one_div_mul_sub_one.tsum_eq
    obtain rfl | hn := eq_or_ne n 0
    · simp
    exact one_div_nonneg.mpr <| mul_nonneg (by positivity) <|
      sub_nonneg.mpr (by exact_mod_cast one_le_iff_ne_zero.mpr hn)
  rw [(summable_one_div_prime_rpow.mpr (by simpa)).tsum_add h₄]
  grw [tsum_prime_rpow_le_log_re_riemannZeta (by simpa), h₅,
    log_re_riemannZeta_le_log_sub_log_sub_one (by simpa), add_sub_cancel_left]

@[pg_tag "bg246" "lem_mertens_tau_k"]
theorem sum_moebius_sq_mul_tau_div_totient_le (k : ℕ) {z : ℕ} (hz : 2 ≤ z) :
    ∑ u ∈ range (z + 1), (μ u ^ 2 * τ k u / φ u : ℝ) ≤ rexp (1 + 3 * k) * .log z ^ k := by
  set κ := (1 + .log z : ℝ)⁻¹ with hκd
  have h₀ : (0 : ℝ) < .log z := log_pos <| Nat.one_lt_cast.mpr hz
  have hκ₀ : 0 < κ := inv_pos.mpr <| by linarith
  have hκ₁ : κ < 1 := inv_lt_one_of_one_lt₀ <| by linarith
  have hκ₂ : -κ.log ≤ 1 + .log (.log z) := by
    rw [hκd, Real.log_inv, neg_neg, Real.log_le_iff_le_exp (by linarith), Real.exp_add,
      Real.exp_log h₀]
    nlinarith [exp_one_gt_d9, log_two_gt_d9, Real.log_le_log two_pos (mod_cast hz : (2 : ℝ) ≤ z)]
  rw [range_eq_Ico, Ico_eq_cons_Ioo z.succ_pos,
    sum_cons, totient_zero, cast_zero, div_zero, zero_add]
  -- Rankin's trick
  have h₁ {u : ℕ} (hu : u ∈ Ioo 0 (z + 1)) : (1 : ℝ) ≤ z ^ κ / u ^ κ := (one_le_div <|
    rpow_pos_of_pos (by simp_all) κ).mpr <| rpow_le_rpow (by positivity) (by simp_all) hκ₀.le
  refine .trans (sum_le_sum fun u hu ↦ le_mul_of_one_le_right (by positivity) <| h₁ hu) ?_
  simp_rw [div_mul_div_comm _ _ (_ ^ _), mul_comm (_ * _), mul_div_assoc _ (_ * _), ← mul_sum]
  have hzκ₁ : (z : ℝ) ^ κ ≤ rexp 1 := (rpow_le_rpow_of_exponent_le (mod_cast hz.trans' one_le_two)
    (hκd.trans_le <| inv_anti₀ h₀ <| by linarith)).trans rpow_inv_log_le_exp_one
  grw [hzκ₁, Real.exp_add, mul_assoc (rexp 1), mul_le_mul_iff_right₀ (exp_pos _),
    (summable_moebius_sq_mul_tau_div_totient_mul_rpow hκ₀).sum_le_tsum _ fun _ _ ↦ by positivity,
    ← (eulerProduct_moebius_sq_mul_tau_div_totient_mul_rpow hκ₀).tprod_eq]
  simp_rw [div_eq_mul_inv, inv_eq_one_div]
  grw [tprod_one_add_le_rexp_tsum
      (fun p ↦ by positivity [show 0 ≤ (p : ℝ) - 1 by simp [p.2.one_le]])
      ((summable_prime_one_div_sub_one_mul_rpow hκ₀).mul_left _),
    tsum_mul_left, tsum_one_div_sub_one_mul_rpow_le hκ₀, hκ₁, one_add_one_eq_two,
    show Real.log 2 < 1 from log_two_lt_d9.trans (by norm_num), sub_eq_add_neg, hκ₂,
    show (k : ℝ) * (1 + (1 + .log (.log z)) + 1) = 3 * k + k * .log (.log z) by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log h₀]

theorem mul_sum_tau_div_totient_le {k R d : ℕ} (hR : 2 ≤ R) (hk : k ≠ 0) :
    d * ∑ r ∈ Ioc 0 R with Squarefree r ∧ d ∣ r, (τ k (r / d) / φ r : ℝ) ≤
    rexp (1 + 3 * k) * Real.log R ^ k := by
  set s := {r ∈ Ioc 0 R | Squarefree r ∧ d ∣ r}
  obtain hs | ⟨r₀, hr₀⟩ := s.eq_empty_or_nonempty
  · simpa [hs] using by positivity
  have hsd : Squarefree d := by grind [(mem_filter.mp hr₀).2, Squarefree.squarefree_of_dvd]
  have hd := hsd.ne_zero
  have h₁ : s ⊆ {r ∈ range (R / d + 1) | Squarefree (d * r)}.image (d * ·) := fun r hr ↦ by
    simp only [s, mem_filter, mem_Ioc, mem_range_succ_iff, mem_image] at hr ⊢
    have := Nat.mul_div_cancel' hr.2.2
    exact ⟨r / d, ⟨Nat.div_le_div_right hr.1.2, (this ▸ hr.2.1 :)⟩, this⟩
  grw [h₁, sum_image (mul_right_injective₀ hd).injOn, sum_filter]
  simp_rw +contextual [← totient_apply, Nat.mul_div_cancel_left _ (by positivity : 0 < d),
    isMultiplicative_totient.map_mul_of_squarefree_mul, cast_mul, div_mul_eq_div_div, ← sum_filter,
    div_right_comm _ (totient d : ℝ), ← sum_div, ← mul_div_assoc, mul_div_right_comm, totient_apply]
  simp_rw [← sum_totient_inv hsd]
  have h₂ {e : ℕ} : (φ e : ℝ)⁻¹ ≤ τ k e / φ e := by
    obtain rfl | he := eq_or_ne e 0
    · simp
    have hte : 1 ≤ τ k e := tau_pos he hk
    grw [← hte, cast_one, inv_eq_one_div]
  grw [h₂]
  set f : ArithmeticFunction ℝ := .pdiv (τ k) totient
  have hf (n) : f n = τ k n / φ n := rfl
  have hmf : f.IsMultiplicative := by aesop
  have hf₀ (n) : 0 ≤ f n := by
    rw [hf]
    positivity
  simp_rw [← hf]
  have hsq {e s : ℕ} (he : e ∣ d) (hs : Squarefree (d * s)) : Squarefree (e * s) :=
    hs.squarefree_of_dvd <| mul_dvd_mul_right he s
  rw [sum_mul_sum, ← sum_product',
    sum_congr rfl fun _ _ ↦ .symm <| hmf.map_mul_of_squarefree_mul (by grind),
    ← sum_image <| (injOn_mul_dvd_product_squarefree (d := d)).mono <| by grind]
  grw [← sum_moebius_sq_mul_tau_div_totient_le _ hR]
  simp_rw [mul_div_assoc, ← sum_filter_squarefree]
  refine sum_le_sum_of_subset_of_nonneg ?_ (by grind)
  simp only [subset_iff, mem_image, mem_product, mem_divisors, mem_filter, mem_range_succ_iff,
    Prod.exists, forall_exists_index, and_imp]
  rintro r e s hed hd₀ hs hsf rfl
  grw [le_of_dvd (by positivity) hed, mul_comm, ← Nat.le_div_iff_mul_le (by positivity), hs]
  simp [hsf.squarefree_of_dvd <| mul_dvd_mul_right hed s]

theorem prod_mul_sum_one_div_prod_totient_le {k R : ℕ} (hR : 2 ≤ R) {d : Fin k → ℕ} :
    (∏ i, d i) * ∑ r ∈ finMulAntidiagLE (Fin k) R with Squarefree (∏ i, r i) ∧ ∀ i, d i ∣ r i,
      (1 / ∏ i, φ (r i) : ℝ) ≤ rexp (1 + 3 * k) * .log R ^ k := by
  set s := {r ∈ finMulAntidiagLE (Fin k) R | Squarefree (∏ i, r i) ∧ ∀ i, d i ∣ r i}
  have hs {r} (hr : r ∈ s) : ∏ i, r i ≤ R ∧ Squarefree (∏ i, r i) ∧ ∏ i, d i ∣ ∏ i, r i := by
    simp only [mem_filter, mem_finMulAntidiagLE_iff, s] at hr
    grind [prod_dvd_prod_of_dvd]
  have hne {r} (hr : r ∈ s) : ∏ i, r i ≠ 0 := (hs hr).2.1.ne_zero
  have hdr {r} (hr : r ∈ s) : ∏ i, d i ≤ ∏ i, r i := le_of_dvd (by grind) (hs hr).2.2
  obtain hs | ⟨r₀, hr₀⟩ := s.eq_empty_or_nonempty
  · simpa [hs] using by positivity
  have hsd : Squarefree (∏ i, d i) := (hs hr₀).2.1.squarefree_of_dvd (hs hr₀).2.2
  simp_rw [← totient_apply]
  rw [sum_congr rfl fun r hr ↦ by
      rw [← isMultiplicative_totient.map_prod_of_squarefree_prod (by grind)],
    sum_comp (fun r' ↦ (1 / totient r' : ℝ)) (fun r : Fin k → ℕ ↦ ∏ i, r i)]
  have h₁ : image (fun r ↦ ∏ i, r i) s ⊆ {r' ∈ Ioc 0 R | Squarefree r' ∧ ∏ i, d i ∣ r'} := by grind
  have h₂ {r' : ℕ} : {r ∈ s | ∏ i, r i = r'} ⊆
      (finMulAntidiag k (r' / ∏ i, d i)).image (fun r i ↦ d i * r i) := fun r hr ↦ by
    simp only [mem_filter, mem_image, mem_finMulAntidiag, Nat.div_ne_zero_iff] at hr ⊢
    obtain ⟨hr, rfl⟩ := hr
    refine ⟨fun i ↦ r i / d i, ⟨Nat.eq_div_of_mul_eq_left hsd.ne_zero ?_, hsd.ne_zero, by grind⟩,
      funext fun i ↦ Nat.mul_div_cancel' <| by grind⟩
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun _ _ ↦ Nat.div_mul_cancel <| by grind
  grw [h₁, h₂, Finset.card_image_le]
  simp_rw [← tau_apply_eq_card_finMulAntidiag, nsmul_eq_mul, ← mul_div_assoc, mul_one]
  obtain rfl | hk := eq_or_ne k 0
  · simp [one_apply, ite_div, show 1 ≤ R by grind]
  exact mul_sum_tau_div_totient_le hR hk

end ArithmeticFunction
