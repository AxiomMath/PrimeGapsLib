/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.EulerProducts

import PrimeGapsTheory.ArithmeticFunction.Estimates
import PrimeGapsTheory.Tactic.PaperTag

/-!
# The constants A and B

Euler-product descriptions and estimates for the arithmetic constants `A` and `B`.

## Main definitions

* `ASummand`: The summand defining `A`.
* `A`: The arithmetic constant `A` as an infinite sum.
* `TInner`: The inner sum `∑_{v ≤ R/d, (v, dW) = 1} μ(v)² / v`.

## Main results

* `A_eq_eulerProduct`: An Euler-product formula for `A`.
* `A_closed_form`: `A M = (1 / zetaTwo) / ∏ p ∈ M.primeFactors, (1 - 1 / p ^ 2)` for `0 < M`.
* `one_div_totient_eq_one_div_mul_sum_moebius_sq_div_totient`: The divisor-sum formula
  `1/φ(u) = (1/u) ∑_{d ∣ u} μ(d)²/φ(d)`.
* `sum_moebius_sq_div_totient_eq_sum_mul_TInner`: The outer decomposition of
  `∑_{u ≤ R, (u, W) = 1} μ(u)²/φ(u)` along the inner sums `TInner`.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

open ArithmeticFunction Finset

/-- The `e`-th summand of `A(M)`. -/
noncomputable def ASummand (M : ℕ) (e : ℕ) : ℝ :=
  if Nat.Coprime e M then (μ e : ℝ) / (e : ℝ) ^ 2 else 0

/-- `A(M)` as a `tsum`. -/
@[pg_tag "bg246" "def_AM"]
noncomputable def A (M : ℕ) : ℝ := ∑' e : ℕ, ASummand M e

/-- The arithmetic-function form of the summand. -/
noncomputable def fM (M : ℕ) : ArithmeticFunction ℝ where
  toFun := ASummand M
  map_zero' := by simp [ASummand]

/-- `fM M e = ASummand M e`. -/
lemma fM_apply (M e : ℕ) : fM M e = ASummand M e := rfl

/-- `fM M` is multiplicative, since `μ` is and the coprimality gate `(·, M) = 1` is. -/
lemma fM_isMultiplicative (M : ℕ) : (fM M).IsMultiplicative := by
  rw [IsMultiplicative]
  refine ⟨by simp [fM_apply, ASummand], fun {m n} hmn ↦ ?_⟩
  simp only [fM_apply, ASummand]
  by_cases hm : Nat.Coprime m M
  · by_cases hn : Nat.Coprime n M
    · have hmu : (μ (m * n) : ℝ) = (μ m : ℝ) * (μ n : ℝ) :=
        mod_cast isMultiplicative_moebius.map_mul_of_coprime hmn
      rw [if_pos (hm.mul_left hn), if_pos hm, if_pos hn, hmu]
      push_cast
      field_simp
    · rw [if_neg hn, mul_zero, if_neg fun h ↦ hn (h.coprime_dvd_left (Dvd.intro_left m rfl))]
  · rw [if_neg hm, zero_mul, if_neg fun h ↦ hm (h.coprime_dvd_left (Dvd.intro n rfl))]

/-- `|fM M e| ≤ 1 / e^2`. -/
lemma abs_fM_le (M e : ℕ) : |fM M e| ≤ 1 / (e : ℝ) ^ 2 := by
  rw [fM_apply, ASummand]
  by_cases h : Nat.Coprime e M
  · rw [if_pos h, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 2)]
    gcongr
    exact mod_cast abs_moebius_le_one (n := e)
  · rw [if_neg h, abs_zero]
    positivity

/-- Absolute summability of `fM M`, by comparison with `∑ 1 / e ^ 2`. -/
lemma summable_norm_fM (M : ℕ) : Summable (fun e ↦ ‖fM M e‖) :=
  Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _)
    (fun e ↦ (Real.norm_eq_abs _).trans_le (abs_fM_le M e)) summable_zetaTwo

/-- The local factor at prime `p`. -/
lemma tsum_fM_prime_pow (M : ℕ) (p : Nat.Primes) : (∑' e : ℕ, fM M ((p : ℕ) ^ e)) =
      (if ¬ ((p : ℕ) ∣ M) then (1 - 1 / (p : ℝ) ^ 2) else 1) := by
  have hp : (p : ℕ).Prime := p.2
  have hvanish : ∀ e ∉ Finset.range 2, fM M ((p : ℕ) ^ e) = 0 := by
    intro e he
    simp only [Finset.mem_range, not_lt] at he
    have hns : ¬ Squarefree ((p : ℕ) ^ e) := by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      rintro ⟨-, he1⟩
      omega
    rw [fM_apply, ASummand]
    by_cases hc : Nat.Coprime ((p : ℕ) ^ e) M
    · rw [if_pos hc, moebius_eq_zero_of_not_squarefree hns]
      simp
    · rw [if_neg hc]
  have hmup : (μ (p : ℕ) : ℝ) = -1 := mod_cast moebius_apply_prime hp
  rw [tsum_eq_sum hvanish, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [pow_zero, pow_one, zero_add, fM_apply, ASummand]
  rw [if_pos (Nat.coprime_one_left M), moebius_apply_one]
  by_cases hdvd : (p : ℕ) ∣ M
  · rw [if_neg fun h ↦ hp.coprime_iff_not_dvd.mp h hdvd, if_neg (not_not.mpr hdvd)]
    norm_num
  · rw [if_pos (hp.coprime_iff_not_dvd.2 hdvd), if_pos hdvd, hmup]
    push_cast
    ring

/-- The series defining `A M` converges absolutely. -/
@[pg_tag "bg246" "lem_AM_converges"]
theorem A_summable (M : ℕ) : Summable (fun e : ℕ ↦ |ASummand M e|) := by
  simpa [Real.norm_eq_abs, fM_apply] using summable_norm_fM M

/-- `|A M| ≤ zetaTwo`. -/
@[pg_tag "bg246" "slem_AM_bound_by_zeta2"]
theorem A_abs_le_zetaTwo (M : ℕ) : |A M| ≤ zetaTwo := by
  have hnorm : Summable (fun e : ℕ ↦ ‖ASummand M e‖) := by
    simpa [Real.norm_eq_abs] using A_summable M
  calc |A M| = ‖∑' e : ℕ, ASummand M e‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' e : ℕ, ‖ASummand M e‖ := norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 :=
        Summable.tsum_le_tsum (fun e ↦ by rw [Real.norm_eq_abs, ← fM_apply]; exact abs_fM_le M e)
          hnorm summable_zetaTwo
    _ = zetaTwo := by rw [zetaTwo]

/-- Euler product for `A M`: the factor at `p` is `1 - 1/p ^ 2` if `p ∤ M`, and `1` otherwise. -/
@[pg_tag "bg246" "slem_AM_euler_product"]
theorem A_eq_eulerProduct (M : ℕ) : HasProd (fun p : Nat.Primes ↦
        if ¬ ((p : ℕ) ∣ M) then (1 - 1 / (p : ℝ) ^ 2) else 1) (A M) := by
  have hAeq : A M = ∑' n : ℕ, fM M n := rfl
  rw [hAeq]
  simpa only [tsum_fM_prime_pow] using
    (fM_isMultiplicative M).eulerProduct_hasProd (summable_norm_fM M)

/-- The Euler product of `(1 - 1/p²)` over ALL primes equals `1/zetaTwo`.
This is the reciprocal of `eulerProduct_zetaTwo : HasProd (fun p => (1-1/p²)⁻¹) zetaTwo`.
Since every factor `(1-1/p²)` and `zetaTwo` are nonzero positive reals, the product
of the reciprocals is the reciprocal of the product. -/
theorem hasProd_oneSubInvSq_all :
    HasProd (fun p : Nat.Primes ↦ (1 - 1 / (p : ℝ) ^ 2)) (1 / zetaTwo) := by
  have hz : zetaTwo ≠ 0 := by
    rw [zetaTwo]
    exact (Summable.tsum_pos summable_zetaTwo (fun n ↦ by positivity) 1 (by norm_num)).ne'
  have htend := Filter.Tendsto.inv₀ eulerProduct_zetaTwo hz
  simp only [Finset.prod_inv_distrib, inv_inv] at htend
  rwa [one_div]

/-- For `0 < M`, `A M = (1 / zetaTwo) / ∏ p ∈ M.primeFactors, (1 - 1 / p ^ 2)`. -/
@[pg_tag "bg246" "slem_AM_value"]
theorem A_closed_form (M : ℕ) (hM : 0 < M) :
    A M = (1 / zetaTwo) / (∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) := by
  have hMne : M ≠ 0 := hM.ne'
  set f : Nat.Primes → ℝ := fun p ↦ (1 - 1 / (p : ℝ) ^ 2) with hf_def
  set s : Set Nat.Primes := {p : Nat.Primes | (p : ℕ) ∣ M} with hs_def
  set g : Nat.Primes → ℝ := fun p ↦ if ¬ ((p : ℕ) ∣ M) then (1 - 1 / (p : ℝ) ^ 2) else 1
    with hg_def
  have hAg : HasProd g (A M) := A_eq_eulerProduct M
  have hfall : HasProd f (1 / zetaTwo) := hasProd_oneSubInvSq_all
  have hg_sub : HasProd (fun x : (sᶜ : Set Nat.Primes) ↦ f x) (A M) := by
    have hsupp : Function.mulSupport g ⊆ sᶜ := by
      intro p hp
      rw [Set.mem_compl_iff, hs_def, Set.mem_ofPred_eq]
      exact fun hdvd ↦ hp (by simp only [hg_def, if_neg (not_not.mpr hdvd)])
    have hsub : HasProd ((g : Nat.Primes → ℝ) ∘ Subtype.val : (sᶜ : Set Nat.Primes) → ℝ) (A M) :=
      (hasProd_subtype_iff_of_mulSupport_subset hsupp).mpr hAg
    have hgf : ((g : Nat.Primes → ℝ) ∘ Subtype.val : (sᶜ : Set Nat.Primes) → ℝ) =
        fun x : (sᶜ : Set Nat.Primes) ↦ f x := by
      funext x
      have hx : ¬ ((x : Nat.Primes) : ℕ) ∣ M := fun hdvd ↦ x.2 hdvd
      simp only [Function.comp, hg_def, hf_def, if_pos hx]
    rwa [hgf] at hsub
  have hfin : (∏' x : s, f x) = ∏ p ∈ M.primeFactors, (1 - 1 / (p : ℝ) ^ 2) := by
    have hprime : ∀ p ∈ M.primeFactors, Nat.Prime p := fun p hp ↦ (Nat.mem_primeFactors.mp hp).1
    let t : Finset Nat.Primes := M.primeFactors.attach.map ⟨fun p ↦ ⟨p.1, hprime p.1 p.2⟩,
        by intro a b hab; ext; simpa using congrArg (fun q ↦ (q : Nat.Primes).1) hab⟩
    have hmem_t : ∀ p : Nat.Primes, p ∈ t ↔ (p : ℕ) ∈ M.primeFactors := by
      intro p
      simp only [t, Finset.mem_map, Finset.mem_attach, true_and, Subtype.exists]
      exact ⟨by rintro ⟨q, hq, rfl⟩; exact hq, fun hp ↦ ⟨(p : ℕ), hp, Subtype.ext rfl⟩⟩
    have hts : (↑t : Set Nat.Primes) = s := by
      ext p
      rw [hs_def]
      simp only [Finset.mem_coe, Set.mem_ofPred_eq]
      rw [hmem_t p, Nat.mem_primeFactors]
      exact ⟨fun h ↦ h.2.1, fun h ↦ ⟨p.2, h, hMne⟩⟩
    rw [← hts, Finset.tprod_subtype' t f]
    exact Finset.prod_bij (fun (p : Nat.Primes) _ ↦ (p : ℕ)) (fun p hp ↦ (hmem_t p).mp hp)
      (fun _ _ _ _ hab ↦ Subtype.ext hab)
      (fun b hb ↦ ⟨⟨b, hprime b hb⟩, (hmem_t _).mpr hb, rfl⟩) (fun _ _ ↦ rfl)
  have hsplit : (∏' x : s, f x) * (∏' x : (sᶜ : Set Nat.Primes), f x) = 1 / zetaTwo := by
    have hs_finite : Finite ↥s := by
      refine Set.Finite.of_finite_image (f := fun p : Nat.Primes ↦ (p : ℕ))
        (Set.Finite.subset M.primeFactors.finite_toSet ?_) (fun _ _ _ _ hab ↦ Subtype.ext hab)
      rintro n ⟨p, hp, rfl⟩
      rw [hs_def, Set.mem_ofPred_eq] at hp
      exact Nat.mem_primeFactors.mpr ⟨p.2, hp, hMne⟩
    have hmul_s : Multipliable (fun x : s ↦ f x) := Multipliable.of_finite
    have hmul_sc : Multipliable (fun x : (sᶜ : Set Nat.Primes) ↦ f x) := hg_sub.multipliable
    have hcomb : (∏' x : s, f x) * (∏' x : (sᶜ : Set Nat.Primes), f x) = ∏' x : Nat.Primes, f x :=
      Multipliable.tprod_mul_tprod_compl hmul_s hmul_sc
    rw [hcomb, hfall.tprod_eq]
  have hne : (∏' x : s, f x) ≠ 0 := by
    rw [hfin, Finset.prod_ne_zero_iff]
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := mod_cast (Nat.mem_primeFactors.mp hp).1.two_le
    have h1 : (1 : ℝ) / (p : ℝ) ^ 2 < 1 := by
      rw [div_lt_one (by positivity)]; nlinarith
    linarith
  rw [← hg_sub.tprod_eq, ← hfin]
  field_simp at hsplit ⊢
  linear_combination hsplit

/-- For every integer `u ≥ 1`, `1/φ(u) = (1/u) * ∑_{d ∣ u} μ(d)²/φ(d)`, where the sum ranges
over the positive divisors of `u`. The identity is stated over `ℚ`. -/
@[pg_tag "bg246" "slem_mu_phi_divisor_sum"]
theorem one_div_totient_eq_one_div_mul_sum_moebius_sq_div_totient (u : ℕ) (hu : 1 ≤ u) :
    (1 : ℚ) / (Nat.totient u) = (1 / (u : ℚ)) *
        ∑ d ∈ u.divisors, (((μ d : ℤ) : ℚ) ^ 2 / (Nat.totient d)) := by
  have hu0 : (u : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [ArithmeticFunction.sum_moebius_sq_div_totient]
  field_simp

/-- The inner sum
`T_d = ∑_{v ≤ R/d, (v, dW) = 1} μ(v)^2 / v`,
where `v` ranges over positive integers with `d * v ≤ R` (equivalently
`v ≤ R/d`) and `gcd(v, dW) = 1`. When `d > R` this sum is empty, so `T_d = 0`. -/
@[pg_tag "bg246" "def_T_d"]
noncomputable def TInner (R W d : ℕ) : ℚ :=
  ∑ v ∈ {v ∈ (Finset.Icc 1 R) | d * v ≤ R ∧ Nat.Coprime v (d * W)},
    ((μ v : ℤ) : ℚ) ^ 2 / (v : ℚ)

/-- For `1 ≤ u`, `∑_{d ∣ u, (d, u/d) = 1} μ(d)²/(d φ d) * μ(u/d)²/(u/d) = μ u ^ 2 / φ u`. -/
lemma pointwise_divisor_identity {u : ℕ} (hu : 1 ≤ u) :
    ∑ d ∈ {d ∈ u.divisors | Nat.Coprime d (u / d)},
        (((μ d : ℤ) : ℚ) ^ 2 / ((d : ℚ) * (Nat.totient d : ℚ))) *
          (((μ (u / d) : ℤ) : ℚ) ^ 2 / ((u / d : ℕ) : ℚ)) =
    ((μ u : ℤ) : ℚ) ^ 2 / (Nat.totient u : ℚ) := by
  have hu0 : u ≠ 0 := by omega
  have hune : (u : ℚ) ≠ 0 := mod_cast hu0
  have hphine : (Nat.totient u : ℚ) ≠ 0 := mod_cast (Nat.totient_pos.mpr (by omega)).ne'
  by_cases hsf : Squarefree u
  · have hfilter : {d ∈ u.divisors | Nat.Coprime d (u / d)} = u.divisors := by
      refine Finset.filter_true_of_mem fun d hd ↦ ?_
      have hdvd : d ∣ u := Nat.dvd_of_mem_divisors hd
      by_contra hc
      obtain ⟨p, hp, hpd, hpud⟩ := Nat.Prime.not_coprime_iff_dvd.mp hc
      have hp2 : p * p ∣ u := by
        rw [← Nat.mul_div_cancel' hdvd]; exact mul_dvd_mul hpd hpud
      have h1 : p = 1 := Nat.isUnit_iff.mp (hsf p hp2)
      have := hp.one_lt
      omega
    have hterm : ∀ d ∈ u.divisors,
        (((μ d : ℤ) : ℚ) ^ 2 / ((d : ℚ) * (Nat.totient d : ℚ))) *
          (((μ (u / d) : ℤ) : ℚ) ^ 2 / ((u / d : ℕ) : ℚ)) =
        (((μ d : ℤ) : ℚ) ^ 2 / (Nat.totient d : ℚ)) * (1 / (u : ℚ)) := by
      intro d hd
      have hdvd : d ∣ u := Nat.dvd_of_mem_divisors hd
      have hdpos : 1 ≤ d := Nat.pos_of_mem_divisors hd
      have hddivpos : 1 ≤ u / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hdpos
      have hmuud : ((μ (u / d) : ℤ) : ℚ) ^ 2 = 1 :=
        mod_cast moebius_sq_eq_one_of_squarefree (hsf.squarefree_of_dvd (Nat.div_dvd_of_dvd hdvd))
      have hdne : (d : ℚ) ≠ 0 := by exact_mod_cast (by omega : d ≠ 0)
      have hudne : ((u / d : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : u / d ≠ 0)
      have hphind : (Nat.totient d : ℚ) ≠ 0 :=
        mod_cast (Nat.totient_pos.mpr (by omega : 0 < d)).ne'
      have hcast : (d : ℚ) * ((u / d : ℕ) : ℚ) = (u : ℚ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hmuud, div_mul_div_comm]
      field_simp
      rw [← hcast]
      ring
    have hsum_eq : (∑ d ∈ u.divisors, (((μ d : ℤ) : ℚ) ^ 2 / (Nat.totient d : ℚ))) =
        (u : ℚ) / (Nat.totient u : ℚ) := by
      have h := one_div_totient_eq_one_div_mul_sum_moebius_sq_div_totient u hu
      field_simp at h ⊢
      linarith
    rw [hfilter, show ((μ u : ℤ) : ℚ) ^ 2 = 1 from
      mod_cast moebius_sq_eq_one_of_squarefree hsf, Finset.sum_congr rfl hterm, ← Finset.sum_mul,
      hsum_eq]
    field_simp
  · rw [moebius_eq_zero_of_not_squarefree hsf]
    simp only [Int.cast_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div]
    refine Finset.sum_eq_zero fun d hd ↦ ?_
    obtain ⟨hdmem, hcop⟩ := Finset.mem_filter.mp hd
    have hprod : ((μ d : ℤ) : ℚ) * ((μ (u / d) : ℤ) : ℚ) = 0 := by
      rw [← Int.cast_mul, ← isMultiplicative_moebius.map_mul_of_coprime hcop,
        Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hdmem),
        moebius_eq_zero_of_not_squarefree hsf, Int.cast_zero]
    have h0 : ((μ d : ℤ) : ℚ) ^ 2 * ((μ (u / d) : ℤ) : ℚ) ^ 2 = 0 := by
      rw [← mul_pow, hprod]; ring
    rw [div_mul_div_comm, h0, zero_div]

/-- `pointwise_divisor_identity` read on the `u`-fiber of `(d, v) ↦ d * v`: `μ u ^ 2 / φ u` is the
sum of `μ(d)²/(d φ d) * μ(v)²/v` over the pairs `(d, v)` of the double sum with `d * v = u`. -/
lemma fiber_eq_pointwise (R W u : ℕ) (hu : u ∈ {u ∈ Finset.Icc 1 R | Nat.Coprime u W}) :
    ((μ u : ℤ) : ℚ) ^ 2 / (Nat.totient u : ℚ) =
    ∑ x ∈ {x ∈ ({u ∈ Finset.Icc 1 R | Nat.Coprime u W}.sigma
              (fun d ↦ {v ∈ Finset.Icc 1 R | d * v ≤ R ∧ Nat.Coprime v (d * W)})) |
              x.1 * x.2 = u},
        (((μ x.1 : ℤ) : ℚ) ^ 2 / ((x.1 : ℚ) * (Nat.totient x.1 : ℚ))) *
          (((μ x.2 : ℤ) : ℚ) ^ 2 / (x.2 : ℚ)) := by
  rw [Finset.mem_filter, Finset.mem_Icc] at hu
  obtain ⟨⟨hu1, huR⟩, huW⟩ := hu
  have hu0 : u ≠ 0 := by omega
  have hquot : ∀ x : Σ _ : ℕ, ℕ, x.1 * x.2 = u → u / x.1 = x.2 := by
    intro x hmul
    have hd0 : 0 < x.1 := Nat.pos_of_ne_zero fun h ↦ by rw [h, zero_mul] at hmul; omega
    rw [← hmul, Nat.mul_div_cancel_left _ hd0]
  rw [← pointwise_divisor_identity hu1]
  symm
  apply Finset.sum_nbij' (i := fun x ↦ x.1) (j := fun d ↦ (⟨d, u / d⟩ : Σ _ : ℕ, ℕ))
  · intro x hx
    rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨-, -, -, hvcop⟩, hmul⟩ := hx
    rw [Finset.mem_filter, Nat.mem_divisors]
    refine ⟨⟨⟨x.2, hmul.symm⟩, hu0⟩, ?_⟩
    rw [hquot x hmul]
    exact (Nat.Coprime.coprime_dvd_right ⟨W, by ring⟩ hvcop).symm
  · intro d hd
    obtain ⟨hdmem, hcop⟩ := Finset.mem_filter.mp hd
    have hdvd : d ∣ u := Nat.dvd_of_mem_divisors hdmem
    have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hdmem
    have hmul : d * (u / d) = u := Nat.mul_div_cancel' hdvd
    have hvdvd : (u / d) ∣ u := Nat.div_dvd_of_dvd hdvd
    have hv1 : 1 ≤ u / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd1
    rw [Finset.mem_filter, Finset.mem_sigma, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨⟨⟨hd1, (Nat.le_of_dvd (by omega) hdvd).trans huR⟩,
      Nat.Coprime.coprime_dvd_left hdvd huW⟩,
      ⟨hv1, (Nat.le_of_dvd (by omega) hvdvd).trans huR⟩, by rw [hmul]; exact huR,
      Nat.Coprime.mul_right hcop.symm (Nat.Coprime.coprime_dvd_left hvdvd huW)⟩, hmul⟩
  · intro x hx
    rw [hquot x (Finset.mem_filter.mp hx).2]
  · exact fun _ _ ↦ rfl
  · intro x hx
    rw [hquot x (Finset.mem_filter.mp hx).2]

/-- For every integer `R ≥ 1` and every squarefree integer `W ≥ 1`,
`∑_{u ≤ R, (u,W)=1} μ(u)^2 / φ(u) = ∑_{d ≤ R, (d,W)=1} μ(d)^2 / (d φ(d)) · T_d`.
Since `μ(d)^2 = 0` for non-squarefree `d` and `T_d = 0` for `d > R`, restricting
the right-hand index set to `[1, R]` loses no nonzero terms. -/
@[pg_tag "bg246" "slem_mertens_W_outer_decomp"]
theorem sum_moebius_sq_div_totient_eq_sum_mul_TInner (R W : ℕ) :
    ∑ u ∈ {u ∈ Finset.Icc 1 R | Nat.Coprime u W},
        ((μ u : ℤ) : ℚ) ^ 2 / (Nat.totient u : ℚ)
    =
    ∑ d ∈ {d ∈ Finset.Icc 1 R | Nat.Coprime d W},
        (((μ d : ℤ) : ℚ) ^ 2 / ((d : ℚ) * (Nat.totient d : ℚ))) * TInner R W d := by
  set U := {u ∈ Finset.Icc 1 R | Nat.Coprime u W} with hU
  set g : ℕ → ℕ → ℚ := fun d v ↦ (((μ d : ℤ) : ℚ) ^ 2 / ((d : ℚ) * (Nat.totient d : ℚ))) *
    (((μ v : ℤ) : ℚ) ^ 2 / (v : ℚ))
  set V : ℕ → Finset ℕ := fun d ↦
    {v ∈ Finset.Icc 1 R | d * v ≤ R ∧ Nat.Coprime v (d * W)} with hV
  have hRHS : ∑ d ∈ U, (((μ d : ℤ) : ℚ) ^ 2 / ((d : ℚ) * (Nat.totient d : ℚ))) *
      TInner R W d = ∑ d ∈ U, ∑ v ∈ V d, g d v :=
    Finset.sum_congr rfl fun d _ ↦ by rw [TInner, Finset.mul_sum]
  have hmaps : ∀ x ∈ U.sigma V, x.1 * x.2 ∈ U := by
    intro x hx
    obtain ⟨hd, hv⟩ := Finset.mem_sigma.mp hx
    rw [hU, Finset.mem_filter, Finset.mem_Icc] at hd ⊢
    rw [hV, Finset.mem_filter, Finset.mem_Icc] at hv
    obtain ⟨⟨hd1, hdR⟩, hdcop⟩ := hd
    obtain ⟨⟨hv1, hvR⟩, hvR2, hvcop⟩ := hv
    exact ⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), hvR2⟩,
      Nat.Coprime.mul_left hdcop (Nat.Coprime.coprime_dvd_right ⟨x.fst, by ring⟩ hvcop)⟩
  rw [hRHS, Finset.sum_sigma' U V g, ← Finset.sum_fiberwise_of_maps_to hmaps fun x ↦ g x.1 x.2]
  exact Finset.sum_congr rfl fun u hu ↦ fiber_eq_pointwise R W u hu

end PrimeGaps
