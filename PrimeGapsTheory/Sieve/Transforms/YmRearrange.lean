/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Algebra.Ring.IsFormallyReal
public import PrimeGapsTheory.ArithmeticFunction.LYTransform.Basic
public import PrimeGapsTheory.Arithmetic.ConvergentSums
public import PrimeGapsTheory.Arithmetic.MaynardWeight

import PrimeGapsTheory.ArithmeticFunction.Estimates
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Rearrangement of the distinguished transform

Rearranges the distinguished-coordinate transform into sums over the primary transformed
weights.

## Main results

* `lem_ym_intermediate`: Expresses the distinguished transform through a
  divisibility-restricted primary transform sum.
* `lem_ym_swap`: Interchanges and evaluates the inner divisor sums.
* `lem_ym_prefactor`: Bounds the multiplicative prefactor.
-/

@[expose] public section

open PrimeGaps
open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta

open scoped ArithmeticFunction.detotient

open scoped BigOperators

/-- `∑_{x ∣ e, (x, r) = 1} μ(x)² / φ(x) = ∏_{p ∣ e, p ∤ r} p / (p - 1)`.  Only the squarefree
divisors of `e` composed of primes not dividing `r` contribute, and their divisor sum is the
Euler product over those primes. -/
private theorem sum_hfun_divisors_coprime_eq_prod {e r : ℕ} (he0 : e ≠ 0) (hr0 : r ≠ 0) :
    (∑ x ∈ {x ∈ e.divisors | r.Coprime x}, hfun x) =
      ∏ p ∈ e.primeFactors \ r.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  set P := e.primeFactors \ r.primeFactors with hP
  set e' := ∏ p ∈ P, p with he'_def
  have hprime : ∀ p ∈ P, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  have hpdvde : ∀ p ∈ P, p ∣ e := fun p hp ↦ Nat.dvd_of_mem_primeFactors (Finset.mem_sdiff.mp hp).1
  have he'pf : e'.primeFactors = P := by rw [he'_def]; exact Nat.primeFactors_prod hprime
  have he'sq : Squarefree e' := by
    rw [he'_def]; exact Nat.squarefree_prod_of_forall_prime hprime
  have he'0 : e' ≠ 0 := he'sq.ne_zero
  have he'dvd : e' ∣ e := by
    rw [he'_def]
    exact Finset.prod_primes_dvd _ (fun p hp ↦ (hprime p hp).prime) (fun p hp ↦ hpdvde p hp)
  have he'cop : r.Coprime e' := by
    rw [Nat.coprime_comm, he'_def]
    apply Nat.Coprime.prod_left
    intro p hp
    have hpp := hprime p hp
    rw [Finset.mem_sdiff] at hp
    rw [hpp.coprime_iff_not_dvd]
    exact fun hpr ↦ hp.2 (by rw [Nat.mem_primeFactors]; exact ⟨hpp, hpr, hr0⟩)
  have hsub : e'.divisors ⊆ {x ∈ e.divisors | r.Coprime x} := by
    intro x hx
    rw [Nat.mem_divisors] at hx
    rw [Finset.mem_filter, Nat.mem_divisors]
    exact ⟨⟨hx.1.trans he'dvd, he0⟩, Nat.Coprime.coprime_dvd_right hx.1 he'cop⟩
  have hzero : ∀ x ∈ {x ∈ e.divisors | r.Coprime x}, x ∉ e'.divisors → hfun x = 0 := by
    intro x hx hxni
    rw [Finset.mem_filter, Nat.mem_divisors] at hx
    obtain ⟨⟨hxe, -⟩, hxcop⟩ := hx
    by_cases hxsq : Squarefree x
    · exfalso; apply hxni
      rw [Nat.mem_divisors]
      refine ⟨?_, he'0⟩
      rw [← Nat.prod_primeFactors_of_squarefree hxsq]
      apply Finset.prod_primes_dvd
      · intro p hp; exact (Nat.prime_of_mem_primeFactors hp).prime
      · intro p hp
        have hpp := Nat.prime_of_mem_primeFactors hp
        have hpx : p ∣ x := Nat.dvd_of_mem_primeFactors hp
        have hpe : p ∣ e := hpx.trans hxe
        have hpQ : p ∉ r.primeFactors := by
          rw [Nat.mem_primeFactors]
          rintro ⟨ - , hpr, -⟩
          exact (Nat.Prime.coprime_iff_not_dvd hpp).mp (hxcop.coprime_dvd_right hpx).symm hpr
        have hmem : p ∈ P := Finset.mem_sdiff.mpr ⟨Nat.mem_primeFactors.mpr ⟨hpp, hpe, he0⟩, hpQ⟩
        rw [← he'pf, Nat.mem_primeFactors] at hmem
        exact hmem.2.1
    · rw [hfun_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hxsq]; simp
  rw [← Finset.sum_subset hsub hzero]
  have hcongr : (∑ x ∈ e'.divisors, hfun x) =
      ∑ x ∈ e'.divisors, ((μ x : ℝ) ^ 2 / (Nat.totient x : ℝ)) :=
    Finset.sum_congr rfl (fun x _ ↦ hfun_apply x)
  rw [hcongr, ArithmeticFunction.sum_moebius_sq_div_totient, Nat.div_totient_eq_prod he'0, he'pf]
  apply Finset.prod_congr rfl
  intro p hp
  have hpprime : p.Prime := hprime p hp
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hpprime.ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by
    exact ne_of_gt (sub_pos.mpr (by exact_mod_cast hpprime.one_lt))
  field_simp

namespace Nat

/-- `∑_{a ∣ d, r ∣ a} μ(a)² / φ(a) = d / (r · φ(d))`, for squarefree `r` dividing `0 < d`. -/
theorem totient_recip_restricted {r d : ℕ} (hr : Squarefree r) (hd : 0 < d) (hrd : r ∣ d) :
    ∑ a ∈ {a ∈ d.divisors | r ∣ a},
        ((μ a : ℝ) ^ 2 / (Nat.totient a : ℝ)) =
      (d : ℝ) / ((r : ℝ) * (Nat.totient d : ℝ)) := by
  have hd0 : d ≠ 0 := hd.ne'
  have hr0 : r ≠ 0 := hr.ne_zero
  set e := d / r with he_def
  have he : d = r * e := by rw [he_def, Nat.mul_div_cancel' hrd]
  have he0 : e ≠ 0 := fun h ↦ hd0 (by rw [he, h, mul_zero])
  set P := d.primeFactors with hP
  set Q := r.primeFactors with hQ
  have hQP : Q ⊆ P := Nat.primeFactors_mono hrd hd0
  have hsum_eq : (∑ a ∈ {a ∈ d.divisors | r ∣ a},
        ((μ a : ℝ) ^ 2 / (Nat.totient a : ℝ))) =
      ∑ a ∈ {a ∈ d.divisors | r ∣ a}, hfun a :=
    Finset.sum_congr rfl (fun a _ ↦ (hfun_apply a).symm)
  rw [hsum_eq]
  have hbij : (∑ a ∈ {a ∈ d.divisors | r ∣ a}, hfun a) =
      ∑ c ∈ e.divisors, hfun (r * c) := by
    apply Finset.sum_nbij' (fun a ↦ a / r) (fun c ↦ r * c)
    · intro a ha
      rw [Finset.mem_filter, Nat.mem_divisors] at ha
      obtain ⟨⟨hadvd, -⟩, hra⟩ := ha
      rw [Nat.mem_divisors]
      exact ⟨by rw [he_def]; exact Nat.div_dvd_div hra hadvd, he0⟩
    · intro c hc
      rw [Nat.mem_divisors] at hc
      rw [Finset.mem_filter, Nat.mem_divisors]
      exact ⟨⟨by rw [he]; exact Nat.mul_dvd_mul_left r hc.1, hd0⟩, Dvd.intro c rfl⟩
    · intro a ha
      rw [Finset.mem_filter] at ha; exact Nat.mul_div_cancel' ha.2
    · intro c _
      rw [Nat.mul_div_cancel_left c (Nat.pos_of_ne_zero hr0)]
    · intro a ha
      rw [Finset.mem_filter] at ha; rw [Nat.mul_div_cancel' ha.2]
  rw [hbij]
  have hterm : ∀ c, hfun (r * c) = hfun r * (if Nat.Coprime r c then hfun c else 0) := by
    intro c
    by_cases h : Nat.Coprime r c
    · rw [if_pos h, hfun_isMultiplicative.map_mul_of_coprime h]
    · rw [if_neg h, mul_zero, hfun_apply]
      rcases Nat.eq_zero_or_pos c with hc | hc
      · subst hc; simp
      have hrc : ¬ Squarefree (r * c) := fun hsq ↦ h (Nat.coprime_of_squarefree_mul hsq)
      rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hrc]; simp
  rw [Finset.sum_congr rfl (fun c _ ↦ hterm c), ← Finset.mul_sum,
    Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have hPQ : P \ Q = e.primeFactors \ Q := by
    ext p
    simp only [Finset.mem_sdiff, hP, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hpp, hpd, -⟩, hpQ⟩
      refine ⟨⟨hpp, ?_, he0⟩, hpQ⟩
      have hpr : ¬ p ∣ r := fun hpr ↦ hpQ (by rw [hQ, Nat.mem_primeFactors]; exact ⟨hpp, hpr, hr0⟩)
      rw [he] at hpd
      exact (hpp.dvd_mul.mp hpd).resolve_left hpr
    · rintro ⟨⟨hpp, hpe, -⟩, hpQ⟩
      exact ⟨⟨hpp, by rw [he]; exact hpe.mul_left r, hd0⟩, hpQ⟩
  have hcore : (∑ x ∈ {x ∈ e.divisors | r.Coprime x}, hfun x) =
      ∏ p ∈ P \ Q, ((p : ℝ) / ((p : ℝ) - 1)) := by
    rw [hPQ]; exact sum_hfun_divisors_coprime_eq_prod he0 hr0
  rw [hcore, hfun_apply]
  have hμr : (μ r : ℝ) ^ 2 = 1 := by
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hr
  rw [hμr]
  have hprimeP : ∀ p ∈ P, p.Prime := by intro p hp; rw [hP, Nat.mem_primeFactors] at hp; exact hp.1
  have hp_ge2 : ∀ p ∈ P, (2 : ℝ) ≤ (p : ℝ) := by
    intro p hp; have := (hprimeP p hp).two_le; exact_mod_cast this
  have hPp1_ne : (∏ p ∈ P, ((p : ℝ) - 1)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
      (fun p hp ↦ by have := hp_ge2 p hp; intro h; rw [sub_eq_zero] at h; linarith [h])
  have hφr : (Nat.totient r : ℝ) = ∏ p ∈ Q, ((p : ℝ) - 1) := by
    rw [hQ]
    have hnat : r.totient = ∏ p ∈ r.primeFactors, (p - 1) := by
      rw [Nat.totient_eq_prod_factorization hr.ne_zero, Finsupp.prod, Nat.support_factorization]
      apply Finset.prod_congr rfl
      intro p hp
      have hle : r.factorization p ≤ 1 :=
        (Nat.squarefree_iff_factorization_le_one hr.ne_zero).mp hr p
      have hge : 1 ≤ r.factorization p := by
        rw [Nat.one_le_iff_ne_zero, ← Finsupp.mem_support_iff, Nat.support_factorization]; exact hp
      rw [le_antisymm hle hge]; simp
    rw [hnat]
    push_cast
    apply Finset.prod_congr rfl
    intro p hp
    rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; push_cast; ring
  have hr_prod : (r : ℝ) = ∏ p ∈ Q, (p : ℝ) := by
    rw [hQ, ← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hr]
  have hsplit_p : (∏ p ∈ P, (p : ℝ)) = (∏ p ∈ Q, (p : ℝ)) * (∏ p ∈ P \ Q, (p : ℝ)) :=
    (Finset.prod_sdiff hQP).symm.trans (mul_comm _ _)
  have hsplit_p1 : (∏ p ∈ P, ((p : ℝ) - 1)) =
      (∏ p ∈ Q, ((p : ℝ) - 1)) * (∏ p ∈ P \ Q, ((p : ℝ) - 1)) :=
    (Finset.prod_sdiff hQP).symm.trans (mul_comm _ _)
  have hd_id : (Nat.totient d : ℝ) * (∏ p ∈ P, (p : ℝ)) = (d : ℝ) * (∏ p ∈ P, ((p : ℝ) - 1)) := by
    have hn := Nat.totient_mul_prod_primeFactors d
    have hc : ((d.totient * ∏ p ∈ d.primeFactors, p : ℕ) : ℝ) =
        ((d * ∏ p ∈ d.primeFactors, (p - 1) : ℕ) : ℝ) := by
      exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) hn
    push_cast at hc
    rw [hP]
    rw [show (∏ p ∈ d.primeFactors, ((p : ℝ) - 1)) = ∏ p ∈ d.primeFactors, (((p - 1 : ℕ)) : ℝ) from
      (Finset.prod_congr rfl (fun p hp ↦ by
        rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le]; push_cast; ring)).symm]
    convert hc using 2
  have hPp1_ne' : (∏ p ∈ Q, ((p : ℝ) - 1)) * (∏ p ∈ P \ Q, ((p : ℝ) - 1)) ≠ 0 := by
    rw [← hsplit_p1]; exact hPp1_ne
  have hPQp1_ne : (∏ p ∈ P \ Q, ((p : ℝ) - 1)) ≠ 0 := right_ne_zero_of_mul hPp1_ne'
  have hQp1_ne : (∏ p ∈ Q, ((p : ℝ) - 1)) ≠ 0 := left_ne_zero_of_mul hPp1_ne'
  have hd' : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hd0
  have hφd_ne : (Nat.totient d : ℝ) ≠ 0 := by
    have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hd0); exact_mod_cast this.ne'
  have hQp_ne : (∏ p ∈ Q, (p : ℝ)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun p hp ↦ by have := hp_ge2 p (hQP hp); positivity)
  rw [Finset.prod_div_distrib, hφr, hr_prod, eq_div_iff (mul_ne_zero hQp_ne hφd_ne)]
  field_simp
  rw [hsplit_p, hsplit_p1] at hd_id
  linear_combination hd_id

end Nat

namespace PrimeGaps

variable {k : ℕ}

/-- The inner `a`-sum over the divisor box `∏ᵢ (dᵢ).divisors` evaluates to `∏_{i ≠ m} dᵢ / φ(dᵢ)`
if `rᵢ ∣ dᵢ` for all `i` and `d_m = 1`, and to `0` otherwise. -/
theorem aux_S_eval (m : Fin k) (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hrm : r m = 1)
    (hrsq : ∀ i, Squarefree (r i)) (d : Fin k → ℕ) (hd : ∀ i, 0 < d i) :
    (∑ a ∈ Fintype.piFinset (fun i ↦ (d i).divisors), (if (∀ i, r i ∣ a i) then
          (∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)
        else 0)) = if (∀ i, r i ∣ d i) ∧ d m = 1 then
          ∏ i ∈ Finset.univ.erase m, (d i : ℝ) / (Nat.totient (d i) : ℝ) else 0 := by
  have hc : ∀ a : Fin k → ℕ, (if (∀ i, r i ∣ a i) then
          (∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)
        else 0) = ∏ i, (if r i ∣ a i then (if i = m then (μ (a i) : ℝ)
          else (μ (a i) : ℝ) ^ 2 * (r i : ℝ) /
            (Nat.totient (a i) : ℝ)) else 0) := by
    intro a
    rw [show (if (∀ i, r i ∣ a i) then
          (∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)
        else 0) = (if (∀ i, r i ∣ a i) then
          ∏ i, (if i = m then (μ (a i) : ℝ)
            else (μ (a i) : ℝ) ^ 2 * (r i : ℝ) / (Nat.totient (a i) : ℝ))
        else 0) by
      congr 1
      rw [show (∏ i ∈ Finset.univ.erase m,
            ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)) =
          ∏ i, (if i = m then (1 : ℝ)
            else ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)) by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), if_pos rfl, one_mul]
        exact (Finset.prod_congr rfl (fun i hi ↦ by rw [if_neg (Finset.ne_of_mem_erase hi)])).symm]
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      by_cases h : i = m <;> simp [h]; ring]
    by_cases h : ∀ i, r i ∣ a i
    · rw [if_pos h]
      apply Finset.prod_congr rfl
      intro i _; rw [if_pos (h i)]
    · rw [if_neg h]
      push Not at h; obtain ⟨j, hj⟩ := h
      exact (Finset.prod_eq_zero (Finset.mem_univ j) (by rw [if_neg hj])).symm
  rw [Finset.sum_congr rfl (fun a _ ↦ hc a)]
  rw [← Finset.prod_univ_sum (fun i ↦ (d i).divisors)
      (fun i x ↦ if r i ∣ x then (if i = m then (μ x : ℝ)
        else (μ x : ℝ) ^ 2 * (r i : ℝ) / (Nat.totient x : ℝ)) else 0)]
  have hTi : ∀ i : Fin k, (∑ x ∈ (d i).divisors,
        (if r i ∣ x then (if i = m then (μ x : ℝ)
          else (μ x : ℝ) ^ 2 * (r i : ℝ) / (Nat.totient x : ℝ)) else 0)) =
      if i = m then (if d m = 1 then (1 : ℝ) else 0)
        else (if r i ∣ d i then (d i : ℝ) / (Nat.totient (d i) : ℝ) else 0) := by
    intro i
    by_cases him : i = m
    · subst him
      simp only [hrm, one_dvd, if_true]
      have h : ((μ * (↑ζ : ArithmeticFunction ℤ))
          (d i) : ℤ) = (1 : ArithmeticFunction ℤ) (d i) := by
        rw [ArithmeticFunction.moebius_mul_coe_zeta]
      rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
      have h2 : (∑ a ∈ (d i).divisors, (μ a : ℝ)) =
          ((∑ a ∈ (d i).divisors, μ a : ℤ) : ℝ) := by push_cast; rfl
      rw [h2, h]; split <;> simp_all
    · simp only [if_neg him]
      rw [← Finset.sum_filter]
      by_cases hrd : r i ∣ d i
      · rw [if_pos hrd]
        rw [show (∑ x ∈ {x ∈ (d i).divisors | r i ∣ x},
            (μ x : ℝ) ^ 2 * (r i : ℝ) / (Nat.totient x : ℝ)) =
            (r i : ℝ) * ∑ x ∈ {x ∈ (d i).divisors | r i ∣ x},
            ((μ x : ℝ) ^ 2 / (Nat.totient x : ℝ)) by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro x _; ring]
        rw [Nat.totient_recip_restricted (hrsq i) (hd i) hrd]
        have hr0 : (r i : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (hr i).ne'
        have hφd : (Nat.totient (d i) : ℝ) ≠ 0 := by have := Nat.totient_pos.mpr (hd i); positivity
        field_simp
      · rw [if_neg hrd]
        apply Finset.sum_eq_zero
        intro x hx
        rw [Finset.mem_filter, Nat.mem_divisors] at hx
        exact absurd (hx.2.trans hx.1.1) hrd
  rw [Finset.prod_congr rfl (fun i _ ↦ hTi i),
    ← Finset.mul_prod_erase _ _ (Finset.mem_univ m), if_pos rfl,
    Finset.prod_congr rfl (s₂ := Finset.univ.erase m)
      (fun i hi ↦ by rw [if_neg (Finset.ne_of_mem_erase hi)])]
  by_cases hdm : d m = 1
  · by_cases hall : ∀ i, r i ∣ d i
    · rw [if_pos hdm, if_pos ⟨hall, hdm⟩, one_mul]
      apply Finset.prod_congr rfl
      intro i _; rw [if_pos (hall i)]
    · rw [if_pos hdm, one_mul, if_neg (by tauto)]
      push Not at hall; obtain ⟨j, hj⟩ := hall
      have hjm : j ∈ Finset.univ.erase m := by
        rw [Finset.mem_erase]; refine ⟨?_, Finset.mem_univ j⟩
        rintro rfl; exact hj (hrm ▸ one_dvd _)
      exact Finset.prod_eq_zero hjm (by rw [if_neg hj])
  · rw [if_neg hdm, if_neg (by tauto), zero_mul]

/-- Rewrite the `a`-finsum as a finite sum over the divisor box `∏ᵢ (dᵢ).divisors`, with `W`
pulled out in front. -/
theorem aux_a_sum (m : Fin k) (r : Fin k → ℕ) (d : Fin k → ℕ) (hd : ∀ i, 0 < d i) (W : ℝ) :
    (∑ᶠ a : Fin k → ℕ, (if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) ∧ (∀ i, a i ∣ d i) then
        ((∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)) * W
       else 0)) = W * ∑ a ∈ Fintype.piFinset (fun i ↦ (d i).divisors), (if (∀ i, r i ∣ a i) then
            (∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
                ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)
          else 0) := by
  rw [finsum_eq_finsetSum_of_support_subset _ (s := Fintype.piFinset (fun i ↦ (d i).divisors))]
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Fintype.mem_piFinset] at ha
    have hdvd : ∀ i, a i ∣ d i := fun i ↦ (Nat.mem_divisors.mp (ha i)).1
    have hapos : ∀ i, 0 < a i := fun i ↦ Nat.pos_of_mem_divisors (ha i)
    by_cases hrc : ∀ i, r i ∣ a i
    · rw [if_pos ⟨hapos, hrc, hdvd⟩, if_pos hrc]; ring
    · rw [if_neg (by tauto), if_neg hrc, mul_zero]
  · intro a ha
    simp only [Function.mem_support] at ha
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    by_contra hcon
    push Not at hcon
    apply ha
    rw [if_neg]
    rintro ⟨_, _, hdvd⟩
    obtain ⟨i, hi⟩ := hcon
    exact hi (Nat.mem_divisors.mpr ⟨hdvd i, (hd i).ne'⟩)

/-- The `a`-summand is supported in the divisor box `∏ᵢ (dᵢ).divisors`, hence has finite support. -/
theorem aux_fin (lam : (Fin k → ℕ) →₀ ℝ) (m : Fin k) (r : Fin k → ℕ) (d : Fin k → ℕ) :
    Function.HasFiniteSupport (fun a : Fin k → ℕ ↦
        if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) ∧ (∀ i, 0 < d i) ∧ (∀ i, a i ∣ d i) then
          ((∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)) *
            (lam d / (∏ i, (d i : ℝ))) else 0) := by
  apply Set.Finite.subset (Fintype.piFinset (fun i ↦ (d i).divisors)).finite_toSet
  intro a ha
  simp only [Function.mem_support] at ha
  rw [Finset.mem_coe, Fintype.mem_piFinset]
  by_contra hcon
  push Not at hcon
  obtain ⟨i, hi⟩ := hcon
  apply ha
  rw [if_neg]
  rintro ⟨_, _, hdpos, hadvd⟩
  exact hi (Nat.mem_divisors.mpr ⟨hadvd i, (hdpos i).ne'⟩)

/-- The rearrangement behind `lem_ym_intermediate`: `∑_{d_m = 1, rᵢ ∣ dᵢ} λ_d / ∏ᵢ φ(dᵢ) =
∑_{rᵢ ∣ aᵢ} (y_a / ∏ᵢ φ(aᵢ)) · ∏_{i ≠ m} μ(aᵢ) rᵢ / φ(aᵢ)`. -/
theorem lem_ym_inner_rearrange {R W : ℕ} (lam : (Fin k → ℕ) →₀ ℝ)
    (hl : lam.HasPermissibleSupport R W) (m : Fin k)
    (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hrm : r m = 1) (hrsq : ∀ i, Squarefree (r i)) :
    lam.sum (fun d ld ↦ if d m = 1 ∧ ∀ i, r i ∣ d i then
          ld / (∏ i, (Nat.totient (d i) : ℝ)) else 0) = ∑ᶠ a : Fin k → ℕ,
          if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) then
            (lToY lam a / (∏ i, (Nat.totient (a i) : ℝ))) * ∏ i ∈ Finset.univ.erase m,
                ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)
          else 0 := by
  rw [Finsupp.sum]
  have hg : ∀ a : Fin k → ℕ, (if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) then
            (lToY lam a / (∏ i, (Nat.totient (a i) : ℝ))) * ∏ i ∈ Finset.univ.erase m,
                ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)
          else 0) = ∑ d ∈ lam.support,
          (if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) ∧ (∀ i, 0 < d i) ∧ (∀ i, a i ∣ d i) then
          ((∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)) *
            (lam d / (∏ i, (d i : ℝ))) else 0) := by
    intro a
    by_cases hca : (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i)
    · rw [if_pos hca]
      obtain ⟨hapos, hrdvd⟩ := hca
      rw [PrimeGaps.lToY_apply hl]
      simp_rw [Int.cast_prod, Int.cast_mul, Int.cast_natCast, Nat.cast_prod]
      rw [show ((∏ i, (μ (a i) : ℝ) * (Nat.totient (a i) : ℝ)) *
            lam.sum (fun d ld ↦ if ∀ i, a i ∣ d i then ld / (∏ i, (d i : ℝ)) else 0)) /
            (∏ i, (Nat.totient (a i) : ℝ)) = (∏ i, (μ (a i) : ℝ)) *
            lam.sum (fun d ld ↦ if ∀ i, a i ∣ d i then ld / (∏ i, (d i : ℝ)) else 0) by
        rw [Finset.prod_mul_distrib]
        have hφ : (∏ i, (Nat.totient (a i) : ℝ)) ≠ 0 := Finset.prod_ne_zero_iff.mpr
            (fun i _ ↦ by have := Nat.totient_pos.mpr (hapos i); positivity)
        field_simp]
      rw [Finsupp.sum, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro d hd
      have hld : lam d ≠ 0 := Finsupp.mem_support_iff.mp hd
      have hsq := hl.squarefree_prod_of_ne_zero hld
      have hdpos : ∀ i, 0 < d i := fun i ↦ Nat.pos_of_ne_zero fun hdi ↦
        hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hdi)
      by_cases hdvd : ∀ i, a i ∣ d i
      · rw [if_pos hdvd, if_pos ⟨hapos, hrdvd, hdpos, hdvd⟩]; ring
      · rw [if_neg hdvd, if_neg (by tauto)]; ring
    · rw [if_neg hca]
      symm
      apply Finset.sum_eq_zero
      intro d _
      rw [if_neg]; rintro ⟨h1, h2, _, _⟩; exact hca ⟨h1, h2⟩
  rw [finsum_congr hg]
  rw [finsum_sum_comm _ _ (fun d _ ↦ aux_fin lam m r d)]
  apply Finset.sum_congr rfl
  intro d hdmem
  by_cases hdpos : ∀ i, 0 < d i
  · rw [show (∑ᶠ a : Fin k → ℕ,
        if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) ∧ (∀ i, 0 < d i) ∧ (∀ i, a i ∣ d i) then
          ((∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)) *
            (lam d / (∏ i, (d i : ℝ))) else 0) = (∑ᶠ a : Fin k → ℕ,
        if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) ∧ (∀ i, a i ∣ d i) then
          ((∏ i, (μ (a i) : ℝ)) * ∏ i ∈ Finset.univ.erase m,
              ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)) *
            (lam d / (∏ i, (d i : ℝ))) else 0) by
      apply finsum_congr; intro a
      by_cases h : (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) ∧ (∀ i, a i ∣ d i)
      · rw [if_pos ⟨h.1, h.2.1, hdpos, h.2.2⟩, if_pos h]
      · rw [if_neg (by tauto), if_neg h]]
    rw [aux_a_sum m r d hdpos (lam d / (∏ i, (d i : ℝ))), aux_S_eval m r hr hrm hrsq d hdpos]
    by_cases hcond : d m = 1 ∧ ∀ i, r i ∣ d i
    · rw [if_pos hcond]
      have hcond' : (∀ i, r i ∣ d i) ∧ d m = 1 := ⟨hcond.2, hcond.1⟩
      obtain ⟨hdm, _⟩ := hcond
      have hdm1 : (d m : ℝ) = 1 := by rw [hdm]; norm_num
      have hφm1 : (Nat.totient (d m) : ℝ) = 1 := by rw [hdm]; norm_num
      have hprodd : (∏ i, (d i : ℝ)) = ∏ i ∈ Finset.univ.erase m, (d i : ℝ) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), hdm1, one_mul]
      have hprodφ : (∏ i, (Nat.totient (d i) : ℝ)) =
          ∏ i ∈ Finset.univ.erase m, (Nat.totient (d i) : ℝ) := by
        rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), hφm1, one_mul]
      rw [hprodd, hprodφ, Finset.prod_div_distrib]
      have hde : (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr (fun i _ ↦ by have := hdpos i; positivity)
      have hφe : (∏ i ∈ Finset.univ.erase m, (Nat.totient (d i) : ℝ)) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr
          (fun i _ ↦ by have := Nat.totient_pos.mpr (hdpos i); positivity)
      rw [if_pos hcond']
      field_simp
    · rw [if_neg hcond, if_neg (by simpa [and_comm] using hcond), mul_zero]
  · have hld : lam d ≠ 0 := Finsupp.mem_support_iff.mp hdmem
    have hsq := hl.squarefree_prod_of_ne_zero hld
    exact (hdpos fun i ↦ Nat.pos_of_ne_zero fun hdi ↦
      hsq.ne_zero (Finset.prod_eq_zero (Finset.mem_univ i) hdi)).elim

/-- `lem_ym_intermediate`: for a `k` -tuple `r` of positive integers with `r_m = 1`,
`y^{(m)}_r = (∏_i μ(r_i) g(r_i)) · ∑_{a: r_i ∣ a_i ∀ i} (y_a / ∏_i φ(a_i))`
` · ∏_{i ≠ m} μ(a_i) r_i / φ(a_i)`. -/
@[pg_tag "bg246" "lem_ym_intermediate"]
theorem lem_ym_intermediate {R W : ℕ} (lam : (Fin k → ℕ) →₀ ℝ)
    (hl : lam.HasPermissibleSupport R W) (m : Fin k)
    (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hrm : r m = 1) :
    ym m lam r = (∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ)) *
        ∑ᶠ a : Fin k → ℕ, if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) then
            (lToY lam a / (∏ i, (Nat.totient (a i) : ℝ))) * ∏ i ∈ Finset.univ.erase m,
                ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ)
          else 0 := by
  rw [PrimeGaps.ym_apply hl]
  simp_rw [Int.cast_prod, Int.cast_mul, Int.cast_natCast, Nat.cast_prod]
  set C : ℝ := ∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ) with hC
  by_cases hC0 : C = 0
  · rw [hC0]; simp
  have hrsq : ∀ i, Squarefree (r i) := by
    intro i
    by_contra hsq
    apply hC0
    rw [hC]
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have : μ (r i) = 0 :=
      ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq
    rw [this]; simp
  congr 1
  exact lem_ym_inner_rearrange lam hl m r hr hrm hrsq
end PrimeGaps

open ArithmeticFunction Finset

namespace PrimeGaps

/-- A divisor of a squarefree number is coprime to its complementary divisor. -/
lemma coprime_complement_of_squarefree {a r : ℕ} (ha_sqfree : Squarefree a)
    (hr_pos : 0 < r) (hr_dvd : r ∣ a) : r.Coprime (a / r) := by
  obtain ⟨e, rfl⟩ := hr_dvd
  rw [Nat.mul_div_cancel_left _ hr_pos]
  exact (Nat.squarefree_mul_iff.mp ha_sqfree).1

/-- For `a = r * e`, reindexing by `f ↦ r * f` turns `∑_{d ∣ a, r ∣ d} F d` into
`∑_{f ∣ e} F (r * f)`. -/
lemma sum_reindex_by_complement
    {a r e : ℕ} (hae : a = r * e) (hr_pos : 0 < r) (he_pos : 0 < e)
    (F : ℕ → ℝ) :
    (∑ d ∈ a.divisors, if r ∣ d then F d else 0) =
    ∑ f ∈ e.divisors, F (r * f) := by
  have ha_ne : a ≠ 0 := hae ▸ Nat.mul_ne_zero hr_pos.ne' he_pos.ne'
  rw [← Finset.sum_filter]
  symm
  refine Finset.sum_bij (fun (f : ℕ) (_ : f ∈ e.divisors) ↦ r * f) ?_ ?_ ?_ (fun _ _ ↦ rfl)
  · intro f hf
    rw [Finset.mem_filter, Nat.mem_divisors]
    rw [Nat.mem_divisors] at hf
    exact ⟨⟨hae ▸ mul_dvd_mul_left r hf.1, ha_ne⟩, ⟨f, rfl⟩⟩
  · intro _ _ _ _ h
    exact Nat.eq_of_mul_eq_mul_left hr_pos h
  · intro d hd
    rw [Finset.mem_filter, Nat.mem_divisors] at hd
    obtain ⟨⟨hda, _⟩, hr_dvd⟩ := hd
    refine ⟨d / r, ?_, Nat.mul_div_cancel' hr_dvd⟩
    rw [Nat.mem_divisors]
    refine ⟨(Nat.mul_dvd_mul_iff_left hr_pos).mp ?_, he_pos.ne'⟩
    rw [Nat.mul_div_cancel' hr_dvd, ← hae]
    exact hda

/-- Multiplicativity of `n ↦ μ(n) n / φ(n)` on coprime arguments. -/
lemma summand_factor {r f : ℕ} (hcop : r.Coprime f) :
    ((μ (r * f) : ℝ) * (↑(r * f)) / Nat.totient (r * f)) =
      ((μ r : ℝ) * r / Nat.totient r) *
        ((μ f : ℝ) * f / Nat.totient f) := by
  rw [isMultiplicative_moebius.map_mul_of_coprime hcop, Nat.totient_mul hcop]
  push_cast
  ring

/-- `∑_{f ∣ e} μ(rf) rf / φ(rf) = (μ(r) r / φ(r)) · ∑_{f ∣ e} μ(f) f / φ(f)`, for `r` coprime
to `e`. -/
lemma factor_inner_sum {r e : ℕ} (hcop : r.Coprime e) : (∑ f ∈ e.divisors,
        (μ (r * f) : ℝ) * (↑(r * f)) / Nat.totient (r * f)) =
    ((μ r : ℝ) * r / Nat.totient r) *
      ∑ f ∈ e.divisors, (μ f : ℝ) * f / Nat.totient f := by
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun f hf ↦
    summand_factor (hcop.coprime_dvd_right (Nat.mem_divisors.mp hf).1)

/-- `(p * e').divisors` is the union of `e'.divisors` and its image under `f ↦ p * f`, for `p`
prime. -/
lemma divisors_eq_union {p e' : ℕ} (hp : p.Prime) :
    (p * e').divisors = e'.divisors ∪ e'.divisors.image (fun f ↦ p * f) := by
  rw [Nat.divisors_mul, hp.divisors,
      show ({1, p} : Finset ℕ) = {1} ∪ {p} by ext; simp [or_comm],
      Finset.union_mul, Finset.singleton_mul, Finset.singleton_mul]
  ext
  simp [Finset.smul_finset_def, mul_comm]

/-- If `p ∤ e'`, the divisors of `e'` are disjoint from their `p`-multiples. -/
lemma divisors_disjoint {p e' : ℕ} (hpe' : ¬ p ∣ e') :
    Disjoint e'.divisors (e'.divisors.image (fun f ↦ p * f)) := by
  rw [Finset.disjoint_left]
  intro g hg hg'
  obtain ⟨hgdvd, _⟩ := Nat.mem_divisors.mp hg
  obtain ⟨f, _, hgf⟩ := Finset.mem_image.mp hg'
  exact hpe' (dvd_trans ⟨f, hgf.symm⟩ hgdvd)

/-- Split a divisor sum over `p * e'` (`p` prime, `p ∤ e'`) into the divisors of `e'` and their
`p`-multiples. -/
lemma divisor_sum_split {p e' : ℕ} (hp : p.Prime) (hpe' : ¬ p ∣ e') :
    (∑ d ∈ (p * e').divisors, (μ d : ℝ) * d / Nat.totient d) =
    (∑ f ∈ e'.divisors, (μ f : ℝ) * f / Nat.totient f) +
    ∑ f ∈ e'.divisors, (μ (p * f) : ℝ) * (↑(p * f)) / Nat.totient (p * f) := by
  rw [divisors_eq_union hp, Finset.sum_union (divisors_disjoint hpe')]
  congr 1
  rw [Finset.sum_image]
  intros _ _ _ _ h
  exact Nat.eq_of_mul_eq_mul_left hp.pos h

/-- For positive squarefree `e`, `∑_{f ∣ e} μ(f) f / φ(f) = μ(e) / φ(e)`. -/
lemma inner_sum_formula {e : ℕ} (he_sqfree : Squarefree e) (he_pos : 0 < e) :
    (∑ f ∈ e.divisors, (μ f : ℝ) * f / Nat.totient f) =
    (μ e : ℝ) / Nat.totient e := by
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    by_cases he1 : e = 1
    · subst he1
      simp
    obtain ⟨p, hp, hp_dvd⟩ := Nat.exists_prime_and_dvd he1
    set e' := e / p with he'_def
    have hpe : e = p * e' := by rw [he'_def, Nat.mul_div_cancel' hp_dvd]
    have he'_pos : 0 < e' := Nat.div_pos (Nat.le_of_dvd he_pos hp_dvd) hp.pos
    have he'_sqfree : Squarefree e' := he_sqfree.squarefree_of_dvd (Nat.div_dvd_of_dvd hp_dvd)
    have hp_not_dvd_e' : ¬ p ∣ e' := fun hdvd ↦
      hp.one_lt.ne' (Nat.isUnit_iff.mp (he_sqfree p (hpe ▸ mul_dvd_mul_left p hdvd)))
    have hcop : p.Coprime e' := hp.coprime_iff_not_dvd.mpr hp_not_dvd_e'
    rw [hpe, divisor_sum_split hp hp_not_dvd_e', factor_inner_sum hcop,
        ih e' (Nat.div_lt_self he_pos hp.one_lt) he'_sqfree he'_pos,
        show (μ (p * e') : ℝ) = (μ p : ℝ) * (μ e' : ℝ) by
          exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hcop,
        show (Nat.totient (p * e') : ℝ) = (Nat.totient p : ℝ) * (Nat.totient e' : ℝ) by
          rw [Nat.totient_mul hcop, Nat.cast_mul],
        show (μ p : ℝ) = -1 by exact_mod_cast moebius_apply_prime hp,
        show (Nat.totient p : ℝ) = (p : ℝ) - 1 by
          rw [Nat.totient_prime hp, Nat.cast_sub hp.one_lt.le, Nat.cast_one]]
    have hφe : (Nat.totient e' : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.totient_pos.mpr he'_pos).ne'
    have hp1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    grind

/-- For coprime `r` and `e`, `(μ(r) r / φ(r)) · (μ(e) / φ(e)) = μ(r e) r / φ(r e)`. -/
lemma combine_final {r e : ℕ} (hcop : r.Coprime e) : ((μ r : ℝ) * r / Nat.totient r) *
      ((μ e : ℝ) / Nat.totient e) =
    (μ (r * e) : ℝ) * r / Nat.totient (r * e) := by
  rw [show (μ (r * e) : ℝ) = (μ r : ℝ) * (μ e : ℝ) by
        exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hcop,
      Nat.totient_mul hcop, Nat.cast_mul]
  field_simp

/-- Single-coordinate version: for squarefree a with r ∣ a, the inner divisor-restricted sum of
μ(d) d / φ(d) equals μ(a) r / φ(a). -/
@[pg_tag "bg246" "lem_ym_eval_d_sum"]
theorem lem_ym_eval_d_sum (a r : ℕ) (ha_sqfree : Squarefree a) (ha_pos : 0 < a)
    (hr_pos : 0 < r) (hr_dvd : r ∣ a) :
    (∑ d ∈ a.divisors, if r ∣ d then
        (μ d : ℝ) * d / Nat.totient d
      else 0) =
    (μ a : ℝ) * r / Nat.totient a := by
  set e := a / r
  have hae : a = r * e := (Nat.mul_div_cancel' hr_dvd).symm
  have he_pos : 0 < e := Nat.div_pos (Nat.le_of_dvd ha_pos hr_dvd) hr_pos
  have hcop : r.Coprime e := coprime_complement_of_squarefree ha_sqfree hr_pos hr_dvd
  have he_sqfree : Squarefree e :=
    ha_sqfree.squarefree_of_dvd ⟨r, by rw [hae]; ring⟩
  rw [sum_reindex_by_complement hae hr_pos he_pos
        (fun d ↦ (μ d : ℝ) * d / Nat.totient d),
      factor_inner_sum hcop,
      inner_sum_formula he_sqfree he_pos,
      combine_final hcop, ← hae]
end PrimeGaps

namespace PrimeGaps

variable {k : ℕ}

/-- Tuple form of `lem_ym_eval_d_sum`: `∑_{rᵢ ∣ dᵢ ∣ aᵢ, d_m = 1} ∏ᵢ μ(dᵢ) dᵢ / φ(dᵢ) =
∏_{i ≠ m} μ(aᵢ) rᵢ / φ(aᵢ)`. -/
theorem ym_swap_inner_d_sum (m : Fin k) (r a : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hrm : r m = 1)
    (ha : ∀ i, 0 < a i) (hasq : ∀ i, Squarefree (a i)) (hra : ∀ i, r i ∣ a i) :
    (∑ᶠ d : Fin k → ℕ, if (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ a i) ∧ d m = 1 then
          ∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)
        else 0) = ∏ i ∈ Finset.univ.erase m,
          ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ) := by
  classical
  let G : Fin k → ℕ → ℝ := fun i x ↦ if r i ∣ x ∧ (i = m → x = 1) then
      (μ x : ℝ) * (x : ℝ) / (Nat.totient x : ℝ) else 0
  have hG : ∀ i x, G i x = if r i ∣ x ∧ (i = m → x = 1) then
        (μ x : ℝ) * (x : ℝ) / (Nat.totient x : ℝ) else 0 := fun _ _ ↦ rfl
  have hbox : ∀ d ∈ Fintype.piFinset (fun i ↦ (a i).divisors),
      (if (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ a i) ∧ d m = 1 then
        ∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ) else 0) =
        ∏ i, G i (d i) := by
    intro d hd
    rw [Fintype.mem_piFinset] at hd
    have hdvd : ∀ i, d i ∣ a i := fun i ↦ (Nat.mem_divisors.mp (hd i)).1
    have hdpos : ∀ i, 0 < d i := fun i ↦ Nat.pos_of_mem_divisors (hd i)
    by_cases hcond : (∀ i, r i ∣ d i) ∧ d m = 1
    · rw [if_pos ⟨hdpos, hcond.1, hdvd, hcond.2⟩]
      refine Finset.prod_congr rfl fun i _ ↦ ?_
      rw [hG]
      rw [if_pos ⟨hcond.1 i, fun him ↦ him ▸ hcond.2⟩]
    · rw [if_neg (by tauto)]
      by_cases hrd : ∀ i, r i ∣ d i
      · have hm : d m ≠ 1 := fun h ↦ hcond ⟨hrd, h⟩
        refine (Finset.prod_eq_zero (Finset.mem_univ m) ?_).symm
        rw [hG, if_neg (by tauto)]
      · push Not at hrd
        obtain ⟨i, hi⟩ := hrd
        refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
        rw [hG, if_neg (by tauto)]
  have hstep1 : (∑ᶠ d : Fin k → ℕ,
        if (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ a i) ∧ d m = 1 then
          ∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ) else 0) =
        ∑ d ∈ Fintype.piFinset (fun i ↦ (a i).divisors), ∏ i, G i (d i) := by
    rw [finsum_eq_finsetSum_of_support_subset _ (s := Fintype.piFinset (fun i ↦ (a i).divisors))]
    · exact Finset.sum_congr rfl hbox
    · intro d hd
      simp only [Function.mem_support] at hd
      rw [Finset.mem_coe, Fintype.mem_piFinset]
      by_contra hcon
      push Not at hcon
      obtain ⟨i, hi⟩ := hcon
      apply hd
      rw [if_neg]
      rintro ⟨hpos, _, hdvd, _⟩
      exact hi (Nat.mem_divisors.mpr ⟨hdvd i, (ha i).ne'⟩)
  rw [hstep1, ← Finset.prod_univ_sum]
  have hm_factor : (∑ x ∈ (a m).divisors, G m x) = 1 := by
    have h1mem : (1 : ℕ) ∈ (a m).divisors := Nat.one_mem_divisors.mpr (ha m).ne'
    rw [← Finset.sum_subset (Finset.singleton_subset_iff.mpr h1mem)]
    · rw [Finset.sum_singleton, hG]
      rw [if_pos ⟨by rw [hrm], fun _ ↦ rfl⟩]
      simp
    · intro x _ hx
      rw [Finset.mem_singleton] at hx
      rw [hG, if_neg]
      rintro ⟨_, h2⟩
      exact hx (h2 rfl)
  have hother : ∀ i ∈ Finset.univ.erase m, (∑ x ∈ (a i).divisors, G i x) =
        ((μ (a i) : ℝ) * (r i : ℝ)) / (Nat.totient (a i) : ℝ) := by
    intro i hi
    have hine : i ≠ m := (Finset.mem_erase.mp hi).1
    have : (∑ x ∈ (a i).divisors, G i x) = ∑ x ∈ (a i).divisors,
            if r i ∣ x then (μ x : ℝ) * (x : ℝ) / (Nat.totient x : ℝ) else 0 := by
      refine Finset.sum_congr rfl fun x _ ↦ ?_
      rw [hG]
      by_cases hrx : r i ∣ x
      · rw [if_pos ⟨hrx, fun him ↦ absurd him hine⟩, if_pos hrx]
      · rw [if_neg (by tauto), if_neg hrx]
    rw [this, lem_ym_eval_d_sum (a i) (r i) (hasq i) (ha i) (hr i) (hra i)]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ m), hm_factor, one_mul]
  exact Finset.prod_congr rfl hother

/-- For a `k`-tuple `r` of positive integers with `r_m = 1`,
`y^{(m)}_r = (∏ᵢ μ(rᵢ) g(rᵢ)) · ∑_{a: rᵢ ∣ aᵢ} (y_a / ∏ᵢ φ(aᵢ)) ·`
` ∑_{d: rᵢ ∣ dᵢ ∣ aᵢ, d_m = 1} ∏ᵢ μ(dᵢ) dᵢ / φ(dᵢ)`. -/
@[pg_tag "bg246" "lem_ym_swap"]
theorem lem_ym_swap {R W : ℕ} (lam : (Fin k → ℕ) →₀ ℝ)
    (hl : lam.HasPermissibleSupport R W) (m : Fin k)
    (r : Fin k → ℕ) (hr : ∀ i, 0 < r i) (hrm : r m = 1) :
    ym m lam r = (∏ i, (μ (r i) : ℝ) * (g (r i) : ℝ)) *
        ∑ᶠ a : Fin k → ℕ, if (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i) then
            (lToY lam a / (∏ i, (Nat.totient (a i) : ℝ))) * ∑ᶠ d : Fin k → ℕ,
                (if (∀ i, 0 < d i) ∧ (∀ i, r i ∣ d i) ∧ (∀ i, d i ∣ a i) ∧ d m = 1 then
                  ∏ i, (μ (d i) : ℝ) * (d i : ℝ) / (Nat.totient (d i) : ℝ)
                else 0)
          else 0 := by
  classical
  rw [lem_ym_intermediate lam hl m r hr hrm]
  congr 1
  refine finsum_congr fun a ↦ ?_
  by_cases hcond : (∀ i, 0 < a i) ∧ (∀ i, r i ∣ a i)
  · rw [if_pos hcond, if_pos hcond]
    by_cases hy : lToY lam a = 0
    · rw [hy]; simp
    · have hasq : ∀ i, Squarefree (a i) := by
        intro i
        by_contra hsq
        apply hy
        exact (hsq (PrimeGaps.squarefree_of_lToY_ne_zero hy i)).elim
      rw [ym_swap_inner_d_sum m r a hr hrm hcond.1 hasq hcond.2]
  · rw [if_neg hcond, if_neg hcond]
end PrimeGaps

namespace PrimeGaps

/-- `(p - 2) * p / (p - 1)^2 = 1 - 1/(p - 1)^2`, for `2 ≤ p`. -/
lemma factor_eq_one_minus (p : ℕ) (hp2 : 2 ≤ p) :
    ((p : ℝ) - 2) * (p : ℝ) / ((p : ℝ) - 1) ^ 2 = 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have hne : ((p : ℝ) - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
  rw [show ((p : ℝ) - 2) * (p : ℝ) = ((p : ℝ) - 1) ^ 2 - 1 by ring, sub_div, div_self hne]

/-- `∏ᵢ (1 - δᵢ) ≤ 1` when `0 ≤ δᵢ ≤ 1`. -/
lemma weierstrass_prod_le_one {ι : Type*} (s : Finset ι) (δ : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ δ i) (h1 : ∀ i ∈ s, δ i ≤ 1) :
    ∏ i ∈ s, (1 - δ i) ≤ 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a t hat ih =>
    rw [Finset.prod_insert hat]
    have ha0 := h0 a (Finset.mem_insert_self a t)
    have h0' : ∀ i ∈ t, 0 ≤ δ i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have h1' : ∀ i ∈ t, δ i ≤ 1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
    have hprod_nn : 0 ≤ ∏ i ∈ t, (1 - δ i) :=
      Finset.prod_nonneg fun i hi ↦ by linarith [h1' i hi]
    nlinarith [ih h0' h1', mul_nonneg ha0 hprod_nn]

/-- Weierstrass product inequality: `1 - ∑ᵢ δᵢ ≤ ∏ᵢ (1 - δᵢ)` when `0 ≤ δᵢ ≤ 1`. -/
lemma weierstrass_lower_bound {ι : Type*} (s : Finset ι) (δ : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ δ i) (h1 : ∀ i ∈ s, δ i ≤ 1) :
    1 - ∑ i ∈ s, δ i ≤ ∏ i ∈ s, (1 - δ i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j t hj ih =>
    have h0t : ∀ i ∈ t, 0 ≤ δ i := fun i hi ↦ h0 i (Finset.mem_insert_of_mem hi)
    have h1t : ∀ i ∈ t, δ i ≤ 1 := fun i hi ↦ h1 i (Finset.mem_insert_of_mem hi)
    have ih' := ih h0t h1t
    have hδj0 := h0 j (Finset.mem_insert_self j t)
    have hδj1 := h1 j (Finset.mem_insert_self j t)
    have hS : 0 ≤ ∑ i ∈ t, δ i := Finset.sum_nonneg h0t
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    nlinarith [mul_le_mul_of_nonneg_right ih' (by linarith : (0 : ℝ) ≤ 1 - δ j), mul_nonneg hS hδj0]

/-- Two-sided form: `|∏ᵢ (1 - δᵢ) - 1| ≤ ∑ᵢ δᵢ` when `0 ≤ δᵢ ≤ 1`. -/
lemma weierstrass_abs {ι : Type*} (s : Finset ι) (δ : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ δ i) (h1 : ∀ i ∈ s, δ i ≤ 1) :
    |(∏ i ∈ s, (1 - δ i)) - 1| ≤ ∑ i ∈ s, δ i := by
  have hSnn : 0 ≤ ∑ i ∈ s, δ i := Finset.sum_nonneg h0
  rw [abs_le]
  exact ⟨by linarith [weierstrass_lower_bound s δ h0 h1],
    by linarith [weierstrass_prod_le_one s δ h0 h1]⟩

/-- `1/n^2 ≤ 1/(n-1) - 1/n` for `2 ≤ n`. -/
lemma one_div_sq_le_diff (n : ℕ) (hn : 2 ≤ n) :
    (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / ((n : ℝ) - 1) - 1 / (n : ℝ) := by
  have h2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [div_sub_div _ _ (by linarith) (by linarith),
      div_le_div_iff₀ (by positivity) (by nlinarith)]
  nlinarith

/-- `∑_{n ∈ Ioc D₀ N} (1/(n-1) - 1/n) = 1/D₀ - 1/N`. -/
lemma telescope_sum_inv (D0 N : ℕ) (hDN : D0 ≤ N) :
    ∑ n ∈ Finset.Ioc D0 N, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) =
      1 / (D0 : ℝ) - 1 / (N : ℝ) := by
  induction N, hDN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
    rw [Finset.sum_Ioc_succ_top hN, ih]
    push_cast
    ring

/-- `∑_{n ∈ Ioc D₀ N} 1/n^2 ≤ 1/D₀` for `1 ≤ D₀`. -/
lemma sum_one_div_sq_le_inv_D0 (D0 N : ℕ) (hD : 1 ≤ D0) :
    ∑ n ∈ Finset.Ioc D0 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤ 1 / (D0 : ℝ) := by
  have hD0pos : (0 : ℝ) < (D0 : ℝ) := by exact_mod_cast hD
  by_cases h : N ≤ D0
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty]
    positivity
  · push Not at h
    have hsum_le : ∑ n ∈ Finset.Ioc D0 N, (1 : ℝ) / (n : ℝ) ^ 2 ≤
          ∑ n ∈ Finset.Ioc D0 N, ((1 : ℝ) / ((n : ℝ) - 1) - 1 / (n : ℝ)) := by
      refine Finset.sum_le_sum fun n hn ↦ ?_
      rw [Finset.mem_Ioc] at hn
      exact one_div_sq_le_diff n (by omega)
    rw [telescope_sum_inv D0 N h.le] at hsum_le
    linarith [show (0 : ℝ) ≤ 1 / (N : ℝ) by positivity]

/-- An absolute `A > 0` with `∑_{p ∈ S} 1/p^2 ≤ A/D₀` for every finite `S` whose elements all
exceed `D₀ ≥ 2`. -/
lemma tail_sum_one_over_sq : ∃ A : ℝ, 0 < A ∧ ∀ D0 : ℕ, 2 ≤ D0 → ∀ S : Finset ℕ, (∀ p ∈ S, D0 < p) →
    ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ A / (D0 : ℝ) := by
  refine ⟨2, by norm_num, fun D0 hD0 S hS ↦ ?_⟩
  have hD0pos : (0 : ℝ) < (D0 : ℝ) := by exact_mod_cast (by omega : 0 < D0)
  by_cases hSne : S.Nonempty
  · set N := S.max' hSne
    have hSsub : S ⊆ Finset.Ioc D0 N := fun p hp ↦ by
      simp only [Finset.mem_Ioc]
      exact ⟨hS p hp, S.le_max' p hp⟩
    have h1 : ∑ p ∈ S, (1 : ℝ) / (p : ℝ) ^ 2 ≤ ∑ n ∈ Finset.Ioc D0 N, (1 : ℝ) / (n : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hSsub fun _ _ _ ↦ by positivity
    have h2 := sum_one_div_sq_le_inv_D0 D0 N (by omega)
    have h3 : (1 : ℝ) / (D0 : ℝ) ≤ 2 / (D0 : ℝ) := by
      gcongr
      norm_num
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hSne
    subst hSne
    simp only [Finset.sum_empty]
    positivity

/-- `1/(p-1)^2 ≤ 4/p^2` for `2 ≤ p`. -/
lemma one_over_sub_one_sq_le_four_over_sq (p : ℕ) (hp : 2 ≤ p) :
    1 / ((p : ℝ) - 1) ^ 2 ≤ 4 / (p : ℝ) ^ 2 := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  rw [div_le_div_iff₀ (by nlinarith) (by positivity)]
  nlinarith

/-- `(∏_{p ∈ n.primeFactors} (p - 2)) * n / φ(n)^2 = ∏_{p ∈ n.primeFactors} (1 - 1/(p-1)^2)`, for
positive squarefree `n`. -/
lemma ratio_eq_prod_one_minus (n : ℕ) (hn : 0 < n) (hsq : Squarefree n) :
    ((∏ p ∈ n.primeFactors, ((p : ℝ) - 2)) * (n : ℝ)) / ((n.totient : ℝ)) ^ 2 =
    ∏ p ∈ n.primeFactors, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rw [squarefree_eq_prod_primes n hsq, totient_eq_prod_sub_one n hn hsq,
      ← Finset.prod_mul_distrib, ← Finset.prod_pow, ← Finset.prod_div_distrib]
  exact Finset.prod_congr rfl fun p hp ↦
    factor_eq_one_minus p (Nat.prime_of_mem_primeFactors hp).two_le

/-- the product `∏ g(rᵢ)·rᵢ/φ(rᵢ)²` is `1 + O(1/D₀)` when every prime factor of each `rᵢ` exceeds
`D₀`. -/
@[pg_tag "bg246" "lem_ym_prefactor"]
theorem lem_ym_prefactor (k : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ D0 : ℕ, 2 ≤ D0 →
      ∀ r : Fin k → ℕ, (∀ i, 0 < r i ∧ Squarefree (r i) ∧ ∀ p ∈ (r i).primeFactors, D0 < p) →
        |((∏ i, (((∏ p ∈ (r i).primeFactors, (p - 2 : ℝ)) * (r i : ℝ)) /
                 (Nat.totient (r i) : ℝ) ^ 2)) - 1)| ≤ C / D0 := by
  obtain ⟨A, hApos, htail⟩ := tail_sum_one_over_sq
  refine ⟨4 * A * k + 1, by positivity, fun D0 hD0 r hr ↦ ?_⟩
  have hD0pos : (0 : ℝ) < (D0 : ℝ) := by exact_mod_cast (by omega : 0 < D0)
  set δ : ℕ → ℝ := fun p ↦ 1 / ((p : ℝ) - 1) ^ 2
  set S : Finset (Σ _ : Fin k, ℕ) :=
    (Finset.univ : Finset (Fin k)).sigma (fun i ↦ (r i).primeFactors)
  have hprod_eq : (∏ i, (((∏ p ∈ (r i).primeFactors, (p - 2 : ℝ)) * (r i : ℝ)) /
            ((r i).totient : ℝ) ^ 2)) =
      ∏ x ∈ S, (1 - δ x.2) := by
    rw [Finset.prod_sigma]
    exact Finset.prod_congr rfl fun i _ ↦ ratio_eq_prod_one_minus (r i) (hr i).1 (hr i).2.1
  rw [hprod_eq]
  have hδ_nonneg : ∀ x ∈ S, 0 ≤ δ x.2 := fun _ _ ↦ by positivity
  have hδ_le_one : ∀ x ∈ S, δ x.2 ≤ 1 := by
    intro x hx
    simp only [S, Finset.mem_sigma, Finset.mem_univ, true_and] at hx
    have hpD0 : D0 < x.2 := (hr x.1).2.2 x.2 hx
    have hp3 : (3 : ℝ) ≤ (x.2 : ℝ) := by exact_mod_cast (by omega : (3 : ℕ) ≤ x.2)
    change 1 / ((x.2 : ℝ) - 1) ^ 2 ≤ 1
    rw [div_le_one (by nlinarith)]
    nlinarith
  have hweier := weierstrass_abs S (fun x ↦ δ x.2) hδ_nonneg hδ_le_one
  have hsum_bound : ∑ x ∈ S, δ x.2 ≤ 4 * A * k / D0 := by
    rw [show ∑ x ∈ S, δ x.2 = ∑ i : Fin k, ∑ p ∈ (r i).primeFactors, δ p by
      simp [S, Finset.sum_sigma]]
    have hinner : ∀ i : Fin k, ∑ p ∈ (r i).primeFactors, δ p ≤ 4 * A / D0 := by
      intro i
      obtain ⟨_, _, hprimes⟩ := hr i
      have hbound1 : ∑ p ∈ (r i).primeFactors, δ p ≤
          4 * ∑ p ∈ (r i).primeFactors, 1 / (p : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have := one_over_sub_one_sq_le_four_over_sq p (Nat.prime_of_mem_primeFactors hp).two_le
        linarith [show 4 * (1 / ((p : ℝ) ^ 2)) = 4 / (p : ℝ) ^ 2 by ring]
      linarith [htail D0 hD0 (r i).primeFactors hprimes,
        mul_le_mul_of_nonneg_left (htail D0 hD0 (r i).primeFactors hprimes)
          (by norm_num : (0 : ℝ) ≤ 4),
        show 4 * (A / (D0 : ℝ)) = 4 * A / D0 by ring]
    calc ∑ i : Fin k, ∑ p ∈ (r i).primeFactors, δ p
        ≤ ∑ _ : Fin k, 4 * A / D0 := Finset.sum_le_sum fun i _ ↦ hinner i
      _ = 4 * A * k / D0 := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
          ring
  have hfinal : 4 * A * k / D0 ≤ (4 * A * k + 1) / D0 :=
    div_le_div_of_nonneg_right (by linarith) hD0pos.le
  linarith [le_trans hweier hsum_bound]
end PrimeGaps


namespace PrimeGaps

/-- For every `k`, every `m: Fin k`, and every finitely-supported `l: (Fin k → ℕ) →₀ ℝ`, the range
of `r ↦ |y^{(m)}(r)|` is bounded above. -/
@[pg_tag "bg246" "lem_ym_max_finite"]
theorem ymMax_finite {k : ℕ} (m : Fin k) (l : (Fin k → ℕ) →₀ ℝ) :
    BddAbove (Set.range (fun r : Fin k → ℕ ↦ |(PrimeGaps.ym m l) r|)) := by
  apply Set.Finite.bddAbove
  have h : (Set.range (fun r : Fin k → ℕ ↦ (PrimeGaps.ym m l) r)).Finite := Finsupp.finite_range _
  have : (Set.range (fun r : Fin k → ℕ ↦ |(PrimeGaps.ym m l) r|))
      ⊆ (fun x : ℝ ↦ |x|) '' (Set.range (fun r : Fin k → ℕ ↦ (PrimeGaps.ym m l) r)) := by
    rintro _ ⟨r, rfl⟩
    exact ⟨(PrimeGaps.ym m l) r, ⟨r, rfl⟩, rfl⟩
  exact Set.Finite.subset (h.image _) this

end PrimeGaps
