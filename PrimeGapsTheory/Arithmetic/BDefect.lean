/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.PSeries
public import PrimeGapsTheory.Arithmetic.MaynardWeight
public import PrimeGapsTheory.Foundations.SieveDatum

import PrimeGapsTheory.Tactic.PaperTag
import PrimeGapsTheory.Arithmetic.Mertens.Shared

/-!
# The multiplicative defect of a Maynard sieve datum

Properties of the multiplicative defect and its associated weighted sums.

## Main definitions

* `bTilde`: The totient-weighted multiplicative defect.

## Main results

* `bDefect_bound`: The defect has quadratic decay at primes.
* `h_eq_sum_bDefect_mul_a`: The sieve weight is the convolution of the defect and totient weight.
* `H_eq_sum_coprime`: The Selberg partial sum is supported on indices coprime to the modulus.
-/

@[expose] public section

open ArithmeticFunction PrimeGaps.MertensShared Real

open scoped ArithmeticFunction.Moebius Finset

namespace PrimeGaps.SieveDatum

variable (S : SieveDatum)

/-- For every prime `p ∤ V`, the defect obeys `|b(p)| ≤ (2 A₃ / A₁) · (1 / p²)`. -/
@[pg_tag "bg246" "slem_b_bound"]
theorem bDefect_bound (p : ℕ) (hp : p.Prime) (hpE : ¬ p ∣ S.V) :
    |S.bDefect p| ≤ (2 * S.A₃ / S.A₁) * (1 / p ^ 2) := by
  rw [S.bDefect_prime_eq p hp hpE]
  have hpR2 : (2 : ℝ) ≤ (p : ℝ) := mod_cast hp.two_le
  have hppos : (0 : ℝ) < (p : ℝ) := by linarith
  have hγlt : S.γ p < p := S.γ_lt p hp
  have hγnn : 0 ≤ S.γ p := S.γ_nonneg p
  have hA1pos : 0 < S.A₁ := S.A₁_pos
  have hA3nn : 0 ≤ S.A₃ := S.A₃_nonneg
  have hden1 : (0 : ℝ) < (p : ℝ) - S.γ p := by linarith
  have hden2 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hdensity : S.γ p / p ≤ 1 - S.A₁ := S.γ_density p hp
  have hlow1 : (p : ℝ) * S.A₁ ≤ (p : ℝ) - S.γ p := by
    nlinarith [(div_le_iff₀ hppos).mp hdensity]
  have hlow2 : (p : ℝ) / 2 ≤ (p : ℝ) - 1 := by linarith
  have hprod_pos : (0 : ℝ) < ((p : ℝ) - S.γ p) * ((p : ℝ) - 1) := mul_pos hden1 hden2
  have hprod_low : (p : ℝ) ^ 2 * (S.A₁ / 2) ≤ ((p : ℝ) - S.γ p) * ((p : ℝ) - 1) := by
    nlinarith [mul_le_mul hlow1 hlow2 (by positivity) (by positivity)]
  have happrox : |S.γ p - 1| ≤ S.A₃ / p := S.γ_approx p hp hpE
  have hnum_abs : |(p : ℝ) * (S.γ p - 1)| ≤ S.A₃ := by
    rw [abs_mul, abs_of_pos hppos]
    calc (p : ℝ) * |S.γ p - 1| ≤ (p : ℝ) * (S.A₃ / p) := by gcongr
      _ = S.A₃ := by field_simp
  rw [abs_div, abs_of_pos hprod_pos, div_le_iff₀ hprod_pos,
    show 2 * S.A₃ / S.A₁ * (1 / (p : ℝ) ^ 2) * (((p : ℝ) - S.γ p) * ((p : ℝ) - 1)) =
      (S.A₃ * (2 / (S.A₁ * (p : ℝ) ^ 2))) * (((p : ℝ) - S.γ p) * ((p : ℝ) - 1)) by ring]
  have h_pfac_bound : ((p : ℝ) - S.γ p) * ((p : ℝ) - 1) * (2 / (S.A₁ * p ^ 2)) ≥ 1 := by
    rw [ge_iff_le, ← div_le_iff₀ (by positivity : (0 : ℝ) < 2 / (S.A₁ * (p : ℝ) ^ 2)),
      show (1 : ℝ) / (2 / (S.A₁ * (p : ℝ) ^ 2)) = (p : ℝ) ^ 2 * (S.A₁ / 2) by field_simp]
    exact hprod_low
  calc |(p : ℝ) * (S.γ p - 1)| ≤ S.A₃ := hnum_abs
    _ = S.A₃ * 1 := by ring
    _ ≤ S.A₃ * (((p : ℝ) - S.γ p) * ((p : ℝ) - 1) * (2 / (S.A₁ * p ^ 2))) :=
        mul_le_mul_of_nonneg_left h_pfac_bound hA3nn
    _ = S.A₃ * (2 / (S.A₁ * p ^ 2)) * (((p : ℝ) - S.γ p) * ((p : ℝ) - 1)) := by ring

/-- The unnormalised `b̃(e) := b(e)·φ(e)/e`.  Multiplicative on coprime inputs,
supported on squarefree `e` coprime to `V`. -/
noncomputable def bTilde (e : ℕ) : ℝ := S.bDefect e * (Nat.totient e : ℝ) / e

/-- `|b̃(e)| ≤ |b(e)|`, since the weight `φ(e)/e` lies in `[0, 1]`. -/
theorem abs_bTilde_le_abs_bDefect (e : ℕ) : |S.bTilde e| ≤ |S.bDefect e| := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [bTilde, bDefect]
  have hfrac_le : (e.totient : ℝ) / e ≤ 1 := by
    rw [div_le_one (mod_cast he)]
    exact_mod_cast Nat.totient_le e
  rw [bTilde, mul_div_assoc, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e.totient : ℝ) / e)]
  exact (mul_le_mul_of_nonneg_left hfrac_le (abs_nonneg _)).trans_eq (mul_one _)

/-- A constant `C` bounding `∑_{e ≤ N} |b(e)| * e.divisors.card * e^(1/2)` for every `N`, obtained
from the local majorant `c / p^(3/2)` at prime powers. -/
private theorem bDefect_tau_sqrt_majorant_bounded : ∃ C : ℝ, 0 < C ∧
      ∀ N : ℕ, ∑ e ∈ Finset.range (N + 1),
        |S.bDefect e| * (#e.divisors : ℝ) * (e : ℝ) ^ ((1 : ℝ) / 2) ≤ C := by
  classical
  set f : ℕ → ℝ := fun e ↦
    |S.bDefect e| * (#e.divisors : ℝ) * (e : ℝ) ^ ((1 : ℝ) / 2) with hf
  set c : ℝ := 4 * S.A₃ / S.A₁ with hc
  set a : ℕ → ℝ := fun n ↦ c * (1 / (n : ℝ) ^ ((3 : ℝ) / 2)) with ha
  have hf_nonneg : ∀ e, 0 ≤ f e := fun e ↦ by rw [hf]; positivity
  have hf_zero_of_not_squarefree : ∀ e, ¬ Squarefree e → f e = 0 := fun e he ↦ by
    simp [hf, S.bDefect_eq_zero_of_not_squarefree e he]
  have hf0 : f 0 = 0 := hf_zero_of_not_squarefree 0 (by simp)
  have hf1 : f 1 = 1 := by simp [hf, bDefect]
  have hf_mul : ∀ {m n : ℕ}, m.Coprime n → f (m * n) = f m * f n := by
    intro m n hmn
    simp only [hf]
    rw [S.bDefect_mul m n hmn, abs_mul, Nat.Coprime.card_divisors_mul hmn]
    push_cast
    rw [Real.mul_rpow (by positivity) (by positivity)]
    ring
  have hf_prime (p : ℕ) (hp : p.Prime) : f p = |S.bDefect p| * 2 * (p : ℝ) ^ ((1 : ℝ) / 2) := by
    simp only [hf]
    rw [hp.divisors, Finset.card_insert_of_notMem (by simp [hp.ne_one.symm]), Finset.card_singleton]
    norm_num
  have hc_nonneg : 0 ≤ c := by
    rw [hc]; exact div_nonneg (mul_nonneg (by norm_num) S.A₃_nonneg) S.A₁_pos.le
  have hf_prime_le (p : ℕ) (hp : p.Prime) : f p ≤ a p := by
    have hpR : (0 : ℝ) < p := mod_cast hp.pos
    rw [hf_prime p hp]
    simp only [ha]
    by_cases hpV : p ∣ S.V
    · rw [S.bDefect_eq_zero_of_not_coprime p fun hc ↦ hp.coprime_iff_not_dvd.mp hc hpV,
        abs_zero, zero_mul, zero_mul]
      exact mul_nonneg hc_nonneg (by positivity)
    have hdef := S.bDefect_bound p hp hpV
    have hstep : |S.bDefect p| * 2 * (p : ℝ) ^ ((1 : ℝ) / 2) ≤
        (2 * S.A₃ / S.A₁ * (1 / (p : ℝ) ^ 2)) * 2 * (p : ℝ) ^ ((1 : ℝ) / 2) := by gcongr
    refine hstep.trans ?_
    rw [show (p : ℝ) ^ (2 : ℕ) = (p : ℝ) ^ (2 : ℝ) by rw [Real.rpow_two, sq],
      show (2 * S.A₃ / S.A₁ * (1 / (p : ℝ) ^ (2 : ℝ))) * 2 * (p : ℝ) ^ ((1 : ℝ) / 2) =
        c * ((p : ℝ) ^ ((1 : ℝ) / 2) / (p : ℝ) ^ (2 : ℝ)) by rw [hc]; ring]
    refine mul_le_mul_of_nonneg_left (le_of_eq ?_) hc_nonneg
    rw [← Real.rpow_sub hpR, show (1 : ℝ) / 2 - 2 = -((3 : ℝ) / 2) by norm_num,
      Real.rpow_neg hpR.le, one_div]
  have hf_prime_pow_zero (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k) : f (p ^ k) = 0 := by
    refine hf_zero_of_not_squarefree _ ?_
    rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
    rintro ⟨_, hk1⟩
    omega
  have hf_prime_pow_summable {p : ℕ} (hp : p.Prime) : Summable (fun k : ℕ ↦ ‖f (p ^ k)‖) := by
    refine summable_of_ne_finset_zero (s := Finset.range 2) fun k hk ↦ ?_
    rw [Finset.mem_range, not_lt] at hk
    rw [hf_prime_pow_zero p k hp hk, norm_zero]
  have ha_nonneg : ∀ n, 0 ≤ a n := fun n ↦ by rw [ha]; positivity
  have ha_summable : Summable a := by
    simpa [ha] using (Real.summable_one_div_nat_rpow.mpr (by norm_num :
      (1 : ℝ) < (3 : ℝ) / 2)).mul_left c
  have hlocal (p : ℕ) (hp : p.Prime) : (∑' k : ℕ, f (p ^ k)) ≤ rexp (a p) := by
    rw [PrimeGaps.MertensShared.tsum_ppow_eq_sum_range f p 2 (hf_prime_pow_zero p · hp),
      Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp only [pow_zero, pow_one, hf1, zero_add]
    calc 1 + f p
        ≤ 1 + a p := by gcongr; exact hf_prime_le p hp
      _ ≤ rexp (a p) := by linarith [Real.add_one_le_exp (a p)]
  refine ⟨rexp (∑' n : ℕ, a n) + 1, by positivity, fun N ↦ ?_⟩
  have hbound := PrimeGaps.MertensShared.finset_sum_le_exp_tsum_of_local
      f hf1 hf0 hf_nonneg
    (fun {_ _} hmn ↦ hf_mul hmn) (fun {_} hp ↦ hf_prime_pow_summable hp)
    a ha_nonneg ha_summable hlocal (Finset.range (N + 1))
  simpa only [hf] using hbound.trans (le_add_of_nonneg_right zero_le_one)

/-- A constant `C` bounding `∑_{e ≤ N} |b̃(e)| * e.divisors.card * e^(1/2)` for every `N`. -/
theorem bDefect_bTilde_tau_sqrt_summable : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∑ e ∈ Finset.range (N + 1),
        |S.bTilde e| * (#e.divisors : ℝ) * (e : ℝ) ^ ((1 : ℝ) / 2) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := S.bDefect_tau_sqrt_majorant_bounded
  refine ⟨C, hC, fun N ↦ (Finset.sum_le_sum fun e _ ↦ ?_).trans (hbound N)⟩
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (S.abs_bTilde_le_abs_bDefect e) (by positivity))
    (Real.rpow_nonneg (Nat.cast_nonneg e) _)

/-- For positive `e` the divisor count is at least one, so `|b̃(e)| ≤ |b̃(e)| * d(e)`. -/
private theorem abs_bTilde_le_mul_card {e : ℕ} (he : 0 < e) :
    |S.bTilde e| ≤ |S.bTilde e| * (#e.divisors : ℝ) := by
  have hcard : (1 : ℝ) ≤ (#e.divisors : ℝ) :=
    mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr he.ne'⟩
  calc |S.bTilde e|
      = |S.bTilde e| * 1 := by ring
    _ ≤ |S.bTilde e| * (#e.divisors : ℝ) := mul_le_mul_of_nonneg_left hcard (abs_nonneg _)

/-- A constant `C` bounding `∑_{e ≤ N} |b̃(e)| * e^(1/4)` for every `N`. -/
theorem bDefect_bTilde_quarter_summable : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∑ e ∈ Finset.range (N + 1),
        |S.bTilde e| * (e : ℝ) ^ ((1 : ℝ) / 4) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := S.bDefect_bTilde_tau_sqrt_summable
  refine ⟨C, hC, fun N ↦ (Finset.sum_le_sum fun e _ ↦ ?_).trans (hbound N)⟩
  rcases Nat.eq_zero_or_pos e with rfl | he
  · simp [bTilde, bDefect]
  calc |S.bTilde e| * (e : ℝ) ^ ((1 : ℝ) / 4)
      ≤ |S.bTilde e| * (e : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_le (mod_cast he) (by norm_num)) (abs_nonneg _)
    _ ≤ |S.bTilde e| * (#e.divisors : ℝ) * (e : ℝ) ^ ((1 : ℝ) / 2) :=
        mul_le_mul_of_nonneg_right (S.abs_bTilde_le_mul_card he)
          (Real.rpow_nonneg (Nat.cast_nonneg e) _)

/-- A constant `C` bounding `∑_{e ≤ N} |b̃(e)| * (1 + log e)` for every `N`. -/
theorem bDefect_bTilde_log_summable : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, ∑ e ∈ Finset.range (N + 1),
        |S.bTilde e| * (1 + Real.log e) ≤ C := by
  obtain ⟨C, hC, hbound⟩ := S.bDefect_bTilde_tau_sqrt_summable
  refine ⟨3 * C, by positivity, fun N ↦ ?_⟩
  calc ∑ e ∈ Finset.range (N + 1), |S.bTilde e| * (1 + Real.log e)
      ≤ ∑ e ∈ Finset.range (N + 1),
          3 * (|S.bTilde e| * (#e.divisors : ℝ) * (e : ℝ) ^ ((1 : ℝ) / 2)) := by
        refine Finset.sum_le_sum fun e _ ↦ ?_
        rcases Nat.eq_zero_or_pos e with rfl | hepos
        · simp [bTilde, bDefect]
        have heRpos : (0 : ℝ) < e := mod_cast hepos
        have hsqrt_ge_one : (1 : ℝ) ≤ √e := by
          simpa using Real.sqrt_le_sqrt (mod_cast hepos : (1 : ℝ) ≤ e)
        have hlog_bound : (1 : ℝ) + Real.log e ≤ 3 * √e := by
          have hlogle := Real.log_le_sub_one_of_pos (by linarith : 0 < √(e : ℝ))
          rw [Real.log_sqrt heRpos.le] at hlogle
          linarith
        rw [← Real.sqrt_eq_rpow]
        calc |S.bTilde e| * (1 + Real.log e)
            ≤ |S.bTilde e| * (3 * √e) :=
              mul_le_mul_of_nonneg_left hlog_bound (abs_nonneg _)
          _ = 3 * (|S.bTilde e| * √e) := by ring
          _ ≤ 3 * (|S.bTilde e| * (#e.divisors : ℝ) * √e) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
                (S.abs_bTilde_le_mul_card hepos) (Real.sqrt_nonneg _)) (by norm_num)
    _ = 3 * ∑ e ∈ Finset.range (N + 1),
          |S.bTilde e| * (#e.divisors : ℝ) * (e : ℝ) ^ ((1 : ℝ) / 2) := by
      simp_rw [Finset.mul_sum]
    _ ≤ 3 * C := by gcongr; exact hbound N

add_to_pg "maynard" "def_a_dens" hfun
/-- `bDefect` packaged as an arithmetic function. -/
noncomputable def bArith : ArithmeticFunction ℝ :=
  ⟨S.bDefect, by
    unfold bDefect
    rw [if_neg]
    rintro ⟨hs, _⟩
    exact not_squarefree_zero hs⟩

/-- `S.bArith n = S.bDefect n`. -/
@[simp] theorem bArith_apply (n : ℕ) : S.bArith n = S.bDefect n :=
  congrFun (ArithmeticFunction.coe_mk _ _) n

/-- `S.bArith` is multiplicative. -/
theorem bArith_mult : S.bArith.IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨?_, ?_⟩
  · simp only [bArith_apply]
    unfold bDefect
    rw [if_pos ⟨squarefree_one, Nat.coprime_one_left S.V⟩]
    simp
  · intro m n _ _ hmn
    simpa using S.bDefect_mul m n hmn

/-- For squarefree `d`, `S.h d = ∏ p ∈ d.primeFactors, S.gStar p`. -/
theorem h_squarefree_eq_prod (d : ℕ) (hd : Squarefree d) :
    S.h d = ∏ p ∈ d.primeFactors, S.gStar p := by
  unfold h
  rw [S.gStar_squarefree_eq_prod d hd, show ((μ d : ℤ) : ℝ) ^ 2 = 1 from
    mod_cast moebius_sq_eq_one_of_squarefree hd, one_mul]

/-- For every squarefree `d ≥ 1` coprime to `V`, the Selberg summand `h` factors
as the Dirichlet convolution `b * a`: `h(d) = ∑_{e ∣ d} b(e) · a(d/e)`. -/
@[pg_tag "bg246" "slem_h_convolution"]
theorem h_eq_sum_bDefect_mul_a
    (d : ℕ) (hd_pos : 1 ≤ d) (hd_sqf : Squarefree d) (hd_cop : Nat.Coprime d S.V) :
    S.h d = ∑ e ∈ d.divisors, S.bDefect e * hfun (d / e) := by
  have hRHS : ∑ e ∈ d.divisors, S.bDefect e * hfun (d / e) = (S.bArith * hfun) d := by
    rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b ↦ S.bArith a * hfun b)]
    exact Finset.sum_congr rfl fun e _ ↦ by simp
  rw [hRHS, ← ArithmeticFunction.IsMultiplicative.prodPrimeFactors_add_of_squarefree
      S.bArith_mult hfun_isMultiplicative hd_sqf,
    ArithmeticFunction.prodPrimeFactors_apply (Nat.one_le_iff_ne_zero.mp hd_pos),
    S.h_squarefree_eq_prod d hd_sqf]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
  have hpV : ¬ p ∣ S.V := fun hpV ↦ hpp.ne_one
    (Nat.eq_one_of_dvd_one (hd_cop ▸ Nat.dvd_gcd (Nat.dvd_of_mem_primeFactors hp) hpV))
  simp only [ArithmeticFunction.add_apply, bArith_apply, hfun_apply]
  rw [show S.bDefect p = S.gStar p - 1 / ((p : ℝ) - 1) by
      rw [S.bDefect_prime p hpp hpV, S.gStar_prime p hpp],
    show ((μ p : ℤ) : ℝ) ^ 2 = 1 from
      mod_cast moebius_sq_eq_one_of_squarefree hpp.squarefree,
    Nat.totient_prime hpp, show ((p - 1 : ℕ) : ℝ) = (p : ℝ) - 1 by
      rw [Nat.cast_sub hpp.one_lt.le]; norm_num]
  ring

/-- For every `z > 0`, `H(z) = ∑_{d < z, (d, V) = 1} h(d)`: restricting the sum
defining `H(z)` to the terms coprime to `V` changes nothing. -/
@[pg_tag "bg246" "slem_h_support"]
theorem H_eq_sum_coprime (z : ℝ) : S.H z = ∑ d ∈ (Finset.range ⌈z⌉₊).filter
        (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z ∧ Nat.Coprime d S.V), S.h d := by
  unfold H
  refine (Finset.sum_subset (fun d hd ↦ ?_) (fun d hd hnd ↦ ?_)).symm
  · simp only [Finset.mem_filter, Finset.mem_range] at hd ⊢
    exact ⟨hd.1, hd.2.1, hd.2.2.1⟩
  · simp only [Finset.mem_filter, Finset.mem_range] at hd hnd
    obtain ⟨hrange, hpos, hlt⟩ := hd
    apply S.h_eq_zero_of_gcd_gt_one
    have hg0 : Nat.gcd d S.V ≠ 0 := fun h0 ↦
      S.V_pos.ne' (Nat.eq_zero_of_gcd_eq_zero_right h0)
    have hg1 : Nat.gcd d S.V ≠ 1 := fun hcop ↦ hnd ⟨hrange, hpos, hlt, hcop⟩
    omega

end PrimeGaps.SieveDatum

end
