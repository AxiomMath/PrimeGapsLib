/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.ConstantsAB
public import PrimeGapsTheory.Arithmetic.Mertens.Shared
public import PrimeGapsTheory.Foundations.SieveDatum

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The leading coefficient of the sieve weight

Arithmetic properties of the leading coefficient associated with the sieve weight `gStar`.

## Main definitions

* `f`: The leading-coefficient function.
* `outerTerm`: The outer summand in the leading-coefficient series.
* `hAux`: The multiplicative summand factoring `outerTerm` as `A W * hAux W d`.

## Main results

* `lem_g_star_well_defined`: The prime values of `gStar` are well defined and nonnegative.
* `main_thm`: The leading-coefficient series equals one.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

/-- The value `g_*(p)` of the Maynard sieve weight at a prime is well defined and nonnegative:
the denominator `p - γ(p)` is strictly positive and `g_*(p) ≥ 0`. -/
@[pg_tag "bg246" "lem_g_star_well_defined"]
theorem lem_g_star_well_defined (S : SieveDatum) (p : ℕ) (hp : p.Prime) :
    0 < (p : ℝ) - S.γ p ∧ 0 ≤ S.gStar p := by
  have hpos : 0 < (p : ℝ) - S.γ p := by linarith [S.γ_lt p hp]
  refine ⟨hpos, ?_⟩
  rw [S.gStar_prime p hp]
  exact div_nonneg (S.γ_nonneg p) hpos.le

open ArithmeticFunction

private theorem cast_sq_sub_one_pos {p : ℕ} (hp : 2 ≤ p) : (0 : ℝ) < (p : ℝ) ^ 2 - 1 := by
  have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  nlinarith

private theorem cast_moebius_sq {d : ℕ} (hd : Squarefree d) : (μ d : ℝ) ^ 2 = 1 := by
  exact_mod_cast moebius_sq_eq_one_of_squarefree hd

private theorem cast_sq_eq_prod_primeFactors {d : ℕ} (hd : Squarefree d) :
    ((d : ℝ) ^ 2) = ∏ p ∈ d.primeFactors, (p : ℝ) ^ 2 := by
  rw [show (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hd], ← Finset.prod_pow]

/-- The leading-coefficient function `f`, depending on a squarefree `W ≥ 1`:
`f(d) = μ(d)^2 / d^2 · A(dW)`. In particular `f(1) = A(W)`. Note that `f` is multiplicative
only up to the normalizing constant `A(W) = f(1)` (see `f_mul`), since in general `A(W) ≠ 1`. -/
@[pg_tag "bg246" "def_f_leading_coeff"]
noncomputable def f (W : ℕ) (d : ℕ) : ℝ := ((μ d : ℝ)) ^ 2 / (d : ℝ) ^ 2 * A (d * W)

/-- The Euler factor product `∏_{p ∣ d} (1 - 1/p²)` is nonzero, each factor being positive. -/
private theorem prod_one_sub_ne_zero (d : ℕ) : ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2) ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun p hp ↦ ?_
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  have h1 : (1 : ℝ) / (p : ℝ) ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
  exact (sub_pos.mpr h1).ne'

/-- `A(dW) * ∏_{p ∣ d} (1 - 1/p²) = A(W)` for coprime squarefree `d`, `W`: the factors of `d` that
`A(dW)` omits are exactly the ones restored by the product. -/
private theorem A_mul_prod (d W : ℕ) (hd : 0 < d) (hW : 0 < W) (hcop : d.Coprime W)
    (hdsq : Squarefree d) (hWsq : Squarefree W) :
    A (d * W) * ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2) = A W := by
  have hdWsq : Squarefree (d * W) := (Nat.squarefree_mul hcop).2 ⟨hdsq, hWsq⟩
  rw [A_closed_form (d * W) (Nat.mul_pos hd hW), A_closed_form W hW,
    Nat.Coprime.primeFactors_mul hcop, Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
  have hPd := prod_one_sub_ne_zero d
  field_simp

/-- `f W d = 0` for non-squarefree `d`, since `μ(d) = 0`. -/
private theorem f_eq_zero_of_not_squarefree (W d : ℕ) (h : ¬ Squarefree d) : f W d = 0 := by
  simp [f, moebius_eq_zero_of_not_squarefree h]

/-- Product formula for `f`. For squarefree `d` coprime to the squarefree `W`,
`f(d) = A(W) · ∏_{p | d} (1/p²)/(1 - 1/p²)` (the product over the distinct primes dividing
`d`, empty when `d = 1`, so `f(1) = A(W)`). -/
@[pg_tag "bg246" "slem_f_closed_form"]
theorem f_prod (W : ℕ) (hW : 0 < W) (hWsq : Squarefree W)
    (d : ℕ) (hd : 0 < d) (hdsq : Squarefree d) (hdW : Nat.Coprime d W) :
    f W d = A W * ∏ p ∈ d.primeFactors, ((1 / (p : ℝ) ^ 2) / (1 - 1 / (p : ℝ) ^ 2)) := by
  have hAdW : A (d * W) = A W / (∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) :=
    (eq_div_iff (prod_one_sub_ne_zero d)).mpr (A_mul_prod d W hd hW hdW hdsq hWsq)
  have hdval : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod]; exact_mod_cast (Nat.prod_primeFactors_of_squarefree hdsq).symm
  have hprodsq : (∏ p ∈ d.primeFactors, (1 / (p : ℝ) ^ 2)) =
      1 / (∏ p ∈ d.primeFactors, (p : ℝ)) ^ 2 := by
    rw [Finset.prod_div_distrib, Finset.prod_const_one, Finset.prod_pow]
  unfold f
  rw [cast_moebius_sq hdsq, hAdW, Finset.prod_div_distrib, hdval, hprodsq]
  ring

/-- Value of `f` at a prime `p ∤ W`: `f(p) = (1/p^2) · A(W)/(1 - 1/p^2)`. -/
@[pg_tag "bg246" "slem_f_prime_value"]
theorem f_prime (W : ℕ) (hW : 0 < W) (hWsq : Squarefree W) (p : ℕ) (hp : p.Prime) (hpW : ¬ p ∣ W) :
    f W p = (1 / (p : ℝ) ^ 2) * (A W / (1 - 1 / (p : ℝ) ^ 2)) := by
  rw [f_prod W hW hWsq p hp.pos hp.squarefree (hp.coprime_iff_not_dvd.mpr hpW), hp.primeFactors,
    Finset.prod_singleton]
  ring

/-- Multiplicativity relation for `f`. For coprime `d₁, d₂` each coprime to the squarefree
`W`, `f(d₁ d₂) · A(W) = f(d₁) · f(d₂)`; this is the division-free form of "`f/A(W)` is
multiplicative". No squarefreeness of `d₁, d₂` is needed: when either factor is
non-squarefree both sides vanish. -/
@[pg_tag "bg246" "slem_f_multiplicative"]
theorem f_mul (W : ℕ) (hW : 0 < W) (hWsq : Squarefree W) (d₁ d₂ : ℕ) (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hcop : Nat.Coprime d₁ d₂) (hW₁ : Nat.Coprime d₁ W) (hW₂ : Nat.Coprime d₂ W) :
    f W (d₁ * d₂) * A W = f W d₁ * f W d₂ := by
  by_cases hsq1 : Squarefree d₁
  · by_cases hsq2 : Squarefree d₂
    · rw [f_prod W hW hWsq (d₁ * d₂) (Nat.mul_pos hd₁ hd₂)
          ((Nat.squarefree_mul hcop).2 ⟨hsq1, hsq2⟩) (Nat.Coprime.mul_left hW₁ hW₂),
        f_prod W hW hWsq d₁ hd₁ hsq1 hW₁, f_prod W hW hWsq d₂ hd₂ hsq2 hW₂,
        Nat.Coprime.primeFactors_mul hcop,
        Finset.prod_union (Nat.Coprime.disjoint_primeFactors hcop)]
      ring
    · rw [f_eq_zero_of_not_squarefree W (d₁ * d₂) fun h ↦ hsq2 ((Nat.squarefree_mul hcop).1 h).2,
        f_eq_zero_of_not_squarefree W d₂ hsq2]
      ring
  · rw [f_eq_zero_of_not_squarefree W (d₁ * d₂) fun h ↦ hsq1 ((Nat.squarefree_mul hcop).1 h).1,
      f_eq_zero_of_not_squarefree W d₁ hsq1]
    ring

open PrimeGaps.MertensShared

open scoped ArithmeticFunction

/-- `A M` unfolds to the tsum of its coprime-Möbius summand `ASummand M`. -/
@[simp] theorem A_eq_tsum_ASummand (M : ℕ) : A M = ∑' e : ℕ, ASummand M e := rfl

/-- `ASummand M` sends `1` to `1`. -/
theorem ASummand_one (M : ℕ) : ASummand M 1 = 1 := by
  simp [ASummand]

/-- `ASummand M` sends `0` to `0`. -/
theorem ASummand_zero (M : ℕ) : ASummand M 0 = 0 := by
  unfold ASummand
  split <;> simp

/-- The coprime-indicator `fun n => if Coprime n N then g n else 0` is multiplicative on
coprime arguments whenever `g` is.  Shared by `ASummand` and `hAux` (which differ only in
their inner Möbius weight `g`). -/
private theorem ite_coprime_mul_of_coprime {N : ℕ} (g : ℕ → ℝ)
    (hgmul : ∀ {a b : ℕ}, Nat.Coprime a b → g (a * b) = g a * g b)
    {m n : ℕ} (h : Nat.Coprime m n) :
    (if Nat.Coprime (m * n) N then g (m * n) else 0) =
      (if Nat.Coprime m N then g m else 0) * (if Nat.Coprime n N then g n else 0) := by
  have hsplit : Nat.Coprime (m * n) N ↔ Nat.Coprime m N ∧ Nat.Coprime n N :=
    Nat.coprime_mul_iff_left
  by_cases hm : Nat.Coprime m N
  · by_cases hn : Nat.Coprime n N
    · rw [if_pos (hsplit.mpr ⟨hm, hn⟩), if_pos hm, if_pos hn, hgmul h]
    · rw [if_neg fun hc ↦ hn (hsplit.mp hc).2, if_neg hn, mul_zero]
  · rw [if_neg fun hc ↦ hm (hsplit.mp hc).1, if_neg hm, zero_mul]

/-- `ASummand M` is multiplicative on coprime arguments. -/
theorem ASummand_mul_of_coprime (M : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    ASummand M (m * n) = ASummand M m * ASummand M n := by
  unfold ASummand
  exact ite_coprime_mul_of_coprime (N := M) (fun e ↦ (μ e : ℝ) / (e : ℝ) ^ 2)
    (fun {a b} hab ↦ by
      have hμ : (μ (a * b) : ℝ) = (μ a : ℝ) * (μ b : ℝ) := by
        exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hab
      rw [hμ]; push_cast; ring) h

/-- The coprime-Möbius series is norm-summable: it is dominated by `∑ 1/e²`. -/
theorem ASummand_summable_norm (M : ℕ) : Summable fun e : ℕ ↦ ‖ASummand M e‖ := by
  have hdom : Summable fun e : ℕ ↦ 1 / (e : ℝ) ^ 2 :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  refine Summable.of_nonneg_of_le (fun e ↦ norm_nonneg _) (fun e ↦ ?_) hdom
  unfold ASummand
  split
  · rw [Real.norm_eq_abs, abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (e : ℝ) ^ 2)]
    have hμ : |(μ e : ℝ)| ≤ 1 := by
      rw [← Int.cast_abs]; exact_mod_cast abs_moebius_le_one (n := e)
    gcongr
  · simp only [norm_zero]
    positivity

/-- Local Euler factor of the coprime-Möbius series at a prime `p`:
`∑' e, ASummand M (p^e) = if p ∣ M then 1 else 1 - 1/p²`. -/
theorem ASummand_local_factor (M : ℕ) (p : Nat.Primes) :
    (∑' e : ℕ, ASummand M ((p : ℕ) ^ e)) = if (p : ℕ) ∣ M then 1 else (1 - 1 / (p : ℝ) ^ 2) := by
  have hp : (p : ℕ).Prime := p.prop
  have hvanish : ∀ e, 2 ≤ e → ASummand M ((p : ℕ) ^ e) = 0 := by
    intro e he2
    have hμ0 : μ ((p : ℕ) ^ e) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega)]
      simp [show e ≠ 1 by omega]
    unfold ASummand
    split
    · rw [hμ0]; simp
    · rfl
  rw [tsum_ppow_eq_sum_range _ _ 2 hvanish, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : ASummand M ((p : ℕ) ^ 0) = 1 := by simpa using ASummand_one M
  rw [h0, pow_one]
  by_cases hdvd : (p : ℕ) ∣ M
  · rw [if_pos hdvd]
    unfold ASummand
    rw [if_neg fun hc ↦ hp.coprime_iff_not_dvd.mp hc hdvd]
    ring
  · rw [if_neg hdvd]
    unfold ASummand
    rw [if_pos (hp.coprime_iff_not_dvd.mpr hdvd), moebius_apply_prime hp]
    push_cast
    ring

/-- Comparing the local Euler factors of `A W` and `A (d * W)` at a prime `p`, for `d ≠ 0`
coprime to `W`: the two factors agree except at the primes dividing `d`, where the factor at
`W` carries the extra factor `1 - 1/p²`.  In other words
`∑' e, ASummand W (p^e) = (if p ∣ d then 1 - 1/p² else 1) · ∑' e, ASummand (d*W) (p^e)`. -/
theorem ASummand_local_factor_eq_ite_mul_local_factor (W : ℕ) {d : ℕ} (hd0 : d ≠ 0)
    (hdW : Nat.Coprime d W) {p : ℕ} (hp : p.Prime) :
    (∑' e : ℕ, ASummand W (p ^ e)) = (if p ∈ d.primeFactors then 1 - 1 / (p : ℝ) ^ 2 else 1) *
        ∑' e : ℕ, ASummand (d * W) (p ^ e) := by
  have hlW : (∑' e : ℕ, ASummand W (p ^ e)) = if p ∣ W then 1 else (1 - 1 / (p : ℝ) ^ 2) :=
    ASummand_local_factor W ⟨p, hp⟩
  have hldW : (∑' e : ℕ, ASummand (d * W) (p ^ e)) =
      if p ∣ (d * W) then 1 else (1 - 1 / (p : ℝ) ^ 2) := ASummand_local_factor (d * W) ⟨p, hp⟩
  rw [hlW, hldW]
  by_cases hpW : p ∣ W
  · have hpd : ¬ p ∣ d := fun hpd ↦
      hp.one_lt.ne' (Nat.eq_one_of_dvd_one (hdW ▸ Nat.dvd_gcd hpd hpW))
    have hmem : p ∉ d.primeFactors := fun h ↦ hpd (Nat.dvd_of_mem_primeFactors h)
    rw [if_pos hpW, if_pos (Dvd.dvd.mul_left hpW d)]
    simp only [hmem, if_false]; ring
  · by_cases hpd : p ∣ d
    · rw [if_neg hpW, if_pos (Dvd.dvd.mul_right hpd W)]
      simp only [Nat.mem_primeFactors.mpr ⟨hp, hpd, hd0⟩, if_true]; ring
    · have hmem : p ∉ d.primeFactors := fun h ↦ hpd (Nat.dvd_of_mem_primeFactors h)
      rw [if_neg hpW, if_neg fun h ↦ (hp.prime.dvd_mul.mp h).elim hpd hpW]
      simp only [hmem, if_false]; ring

/-- The sum form of `A(M)` equals its product form `∏_{p ∤ M} (1 - 1/p²)`: the Euler-product
identity justifying that `A` is the intended constant `A(M)`. -/
theorem A_eq_prod (M : ℕ) :
    A M = ∏' p : Nat.Primes, if (p : ℕ) ∣ M then 1 else (1 - 1 / (p : ℝ) ^ 2) := by
  refine (A_eq_eulerProduct M).tprod_eq.symm.trans (tprod_congr fun p ↦ ?_)
  by_cases h : (p : ℕ) ∣ M <;> simp [h]

/-- The outer summand for `main_thm`: for `d` coprime to `W`,
`(μ(d)²/d²)·A(dW)`, and `0` otherwise. -/
noncomputable def outerTerm (W d : ℕ) : ℝ :=
  if Nat.Coprime d W then
    ((μ d : ℝ) ^ 2 / (d : ℝ) ^ 2) * A (d * W)
  else 0

/-- Rewrites the `main_thm` left-hand side as the tsum of `outerTerm W`.

Deliberately not a `simp` lemma: it rewrites *towards* the definition `outerTerm`, whereas the
simp normal form here unfolds `outerTerm` (and, via `A_eq_tsum_ASummand`, unfolds `A` as well).
It is meant for explicit `rw` at the head of `main_thm`. -/
theorem main_thm_lhs_eq (W : ℕ) : (∑' d : ℕ, (if Nat.Coprime d W then
        ((μ d : ℝ) ^ 2 / (d : ℝ) ^ 2) * A (d * W)
      else 0)) = ∑' d : ℕ, outerTerm W d := rfl

/-- Per-term product identity.  For squarefree `d` coprime to `W`,
`(μ(d)²/d²)·A(dW) = A(W) · ∏_{p|d} (1/(p²-1))`, equivalently
`outerTerm W d = A(W) · g d` where `g` is the multiplicative function with
`g(p) = 1/(p²-1)` for `p ∤ W` (and, as we only ever hit squarefree `d` coprime to
`W`, `g(p^e)=0` for `e≥2` and `g(p)=0`/irrelevant for `p|W`). -/
theorem outerTerm_factor (W : ℕ) {d : ℕ} (hd : Squarefree d) (hdW : Nat.Coprime d W) :
    outerTerm W d = (A W) * ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) ^ 2 - 1)) := by
  classical
  set FW : ℕ → ℝ :=
    Set.mulIndicator {p | Nat.Prime p} (fun p ↦ ∑' e : ℕ, ASummand W ((p : ℕ) ^ e)) with hFW
  set FdW : ℕ → ℝ :=
    Set.mulIndicator {p | Nat.Prime p} (fun p ↦ ∑' e : ℕ, ASummand (d * W) ((p : ℕ) ^ e)) with hFdW
  have hpW : HasProd FW (∑' n : ℕ, ASummand W n) :=
    EulerProduct.eulerProduct_hasProd_mulIndicator (ASummand_one W)
      (fun {m n} h ↦ ASummand_mul_of_coprime W h) (ASummand_summable_norm W) (ASummand_zero W)
  have hpdW : HasProd FdW (∑' n : ℕ, ASummand (d * W) n) :=
    EulerProduct.eulerProduct_hasProd_mulIndicator (ASummand_one (d * W))
      (fun {m n} h ↦ ASummand_mul_of_coprime (d * W) h) (ASummand_summable_norm (d * W))
      (ASummand_zero (d * W))
  set E : ℕ → ℝ := fun n ↦ if n ∈ d.primeFactors then (1 - 1 / (n : ℝ) ^ 2) else 1 with hE
  have hpE : HasProd E (∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) := by
    have hh : HasProd E (∏ b ∈ d.primeFactors, E b) :=
      hasProd_prod_of_ne_finset_one (f := E) (s := d.primeFactors)
        (fun b hb ↦ by simp only [hE, if_neg hb])
    have hfin : (∏ b ∈ d.primeFactors, E b) = ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2) :=
      Finset.prod_congr rfl fun b hb ↦ by simp only [hE, if_pos hb]
    rwa [hfin] at hh
  have hpoint : ∀ n : ℕ, FW n = E n * FdW n := by
    intro n
    by_cases hn : n.Prime
    · have hmem : n ∈ {p | Nat.Prime p} := hn
      rw [hFW, hFdW, Set.mulIndicator_of_mem hmem, Set.mulIndicator_of_mem hmem, hE]
      exact ASummand_local_factor_eq_ite_mul_local_factor W hd.ne_zero hdW hn
    · have hmem : n ∉ {p | Nat.Prime p} := hn
      have hnfac : n ∉ d.primeFactors := fun h ↦ hn (Nat.prime_of_mem_primeFactors h)
      rw [hFW, hFdW, Set.mulIndicator_of_notMem hmem, Set.mulIndicator_of_notMem hmem, hE]
      simp only [hnfac, if_false]; ring
  have hcombine : HasProd FW
      ((∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) * (∑' n : ℕ, ASummand (d * W) n)) := by
    simpa only [← hpoint] using hpE.mul hpdW
  have hkey : A W = (∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2)) * A (d * W) :=
    hpW.unique hcombine
  rw [outerTerm, if_pos hdW, hkey]
  set P : ℝ := ∏ p ∈ d.primeFactors, (1 - 1 / (p : ℝ) ^ 2) with hP
  set Q : ℝ := ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) ^ 2 - 1)) with hQ
  have hPQ : P * Q = ∏ p ∈ d.primeFactors, (1 / (p : ℝ) ^ 2) := by
    rw [hP, hQ, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp ↦ ?_
    have hne : (p : ℝ) ^ 2 - 1 ≠ 0 :=
      (cast_sq_sub_one_pos (Nat.prime_of_mem_primeFactors hp).two_le).ne'
    have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).pos.ne'
    field_simp
  have hgoal : (μ d : ℝ) ^ 2 / (d : ℝ) ^ 2 = P * Q := by
    rw [cast_moebius_sq hd, cast_sq_eq_prod_primeFactors hd, hPQ, Finset.prod_div_distrib,
      Finset.prod_const_one]
  rw [hgoal]; ring

/-- The per-prime "combining" identity that produces the all-ones factor: for `p ∤ W`,
`(1 - 1/p²) · (1 + 1/(p²-1)) = 1`, i.e. after multiplying the constant `A(W)` factor
into each Euler factor, the local factor at `p ∤ W` collapses to `1`. -/
theorem local_combine (p : ℕ) (hp : 1 < p) :
    (1 - 1 / (p : ℝ) ^ 2) * (1 + 1 / ((p : ℝ) ^ 2 - 1)) = 1 := by
  have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := (cast_sq_sub_one_pos hp).ne'
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp
  ring

/-- Auxiliary multiplicative summand `h d` for the outer Euler product.  For all `d`
this satisfies `outerTerm W d = A(W) · hAux W d`; only squarefree `d` coprime to `W`
contribute (the `μ(d)²` kills non-squarefree `d`, the indicator kills `d` not coprime
to `W`). -/
noncomputable def hAux (W d : ℕ) : ℝ :=
  if Nat.Coprime d W then
    (μ d : ℝ) ^ 2 * ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) ^ 2 - 1))
  else 0

/-- `outerTerm W d = A(W) · hAux W d` for every `d`. -/
theorem outerTerm_eq_const_mul_hAux (W : ℕ) (d : ℕ) : outerTerm W d = A W * hAux W d := by
  classical
  by_cases hdW : Nat.Coprime d W
  · by_cases hd : Squarefree d
    · rw [outerTerm_factor W hd hdW, hAux, if_pos hdW, cast_moebius_sq hd, one_mul]
    · rw [outerTerm, if_pos hdW, hAux, if_pos hdW,
        show (μ d : ℝ) = 0 by exact_mod_cast moebius_eq_zero_of_not_squarefree hd]
      ring
  · rw [outerTerm, if_neg hdW, hAux, if_neg hdW, mul_zero]

/-- `hAux W 1 = 1`. -/
theorem hAux_one (W : ℕ) : hAux W 1 = 1 := by
  simp [hAux]

/-- `hAux W 0 = 0`. -/
theorem hAux_zero (W : ℕ) : hAux W 0 = 0 := by
  simp [hAux]

/-- `hAux W` is multiplicative on coprime arguments. -/
theorem hAux_mul_of_coprime (W : ℕ) {m n : ℕ} (h : Nat.Coprime m n) :
    hAux W (m * n) = hAux W m * hAux W n := by
  unfold hAux
  exact ite_coprime_mul_of_coprime (N := W)
    (fun d ↦ (μ d : ℝ) ^ 2 * ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) ^ 2 - 1)))
    (fun {a b} hab ↦ by
      rcases Nat.eq_zero_or_pos a with ha0 | ha0
      · subst ha0
        obtain rfl : b = 1 := (Nat.coprime_zero_left b).mp hab
        simp
      rcases Nat.eq_zero_or_pos b with hb0 | hb0
      · subst hb0
        obtain rfl : a = 1 := (Nat.coprime_zero_right a).mp hab
        simp
      have hμ : (μ (a * b) : ℝ) = (μ a : ℝ) * (μ b : ℝ) := by
        exact_mod_cast isMultiplicative_moebius.map_mul_of_coprime hab
      have hprod : (∏ p ∈ (a * b).primeFactors, (1 / ((p : ℝ) ^ 2 - 1))) =
          (∏ p ∈ a.primeFactors, (1 / ((p : ℝ) ^ 2 - 1))) *
              (∏ p ∈ b.primeFactors, (1 / ((p : ℝ) ^ 2 - 1))) := by
        rw [Nat.primeFactors_mul ha0.ne' hb0.ne',
          Finset.prod_union (Nat.Coprime.disjoint_primeFactors hab)]
      rw [hμ, hprod]; ring) h

end PrimeGaps

namespace Finset

/-- Telescoping product: `∏_{k=2}^{N} k²/(k²-1) = 2N/(N+1)`. -/
theorem prod_Icc_sq_div_sq_sub_one (N : ℕ) (hN : 2 ≤ N) :
    (∏ k ∈ Finset.Icc 2 N, ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1))) = 2 * (N : ℝ) / ((N : ℝ) + 1) := by
  induction N with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge n 2 with hn | hn
    · interval_cases n
      · omega
      · rw [Finset.Icc_self, Finset.prod_singleton]
        norm_num
    · rw [Finset.prod_Icc_succ_top (by omega), ih hn]
      have hn0 : (n : ℝ) + 1 ≠ 0 := by positivity
      have hn1 : ((n : ℝ) + 1) ^ 2 - 1 ≠ 0 := by
        have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        nlinarith
      push_cast
      field_simp
      ring

end Finset

namespace Nat

/-- Bound: for `d ≠ 0`, `∏_{p|d} p²/(p²-1) ≤ 2`. -/
theorem prod_primeFactors_sq_div_sq_sub_one_le_two {d : ℕ} (hd : d ≠ 0) :
    (∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1))) ≤ 2 := by
  classical
  have hd0 : 0 < d := Nat.pos_of_ne_zero hd
  have hsub : d.primeFactors ⊆ Finset.Icc 2 d := fun p hp ↦ Finset.mem_Icc.mpr
    ⟨(Nat.prime_of_mem_primeFactors hp).two_le, Nat.le_of_dvd hd0 (Nat.dvd_of_mem_primeFactors hp)⟩
  have hfge1 : ∀ k ∈ Finset.Icc 2 d, (1 : ℝ) ≤ (k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1) := by
    intro k hk
    rw [le_div_iff₀ (PrimeGaps.cast_sq_sub_one_pos (Finset.mem_Icc.mp hk).1)]
    linarith
  have hprimenn : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) :=
    Finset.prod_nonneg fun p hp ↦ zero_le_one.trans (hfge1 p (hsub hp))
  have hle : (∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1))) ≤
      (∏ k ∈ Finset.Icc 2 d, ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1))) := by
    rw [← Finset.prod_sdiff hsub]
    have hsdiff : (1 : ℝ) ≤
        ∏ k ∈ Finset.Icc 2 d \ d.primeFactors, ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) := by
      have h1 : (∏ _ ∈ Finset.Icc 2 d \ d.primeFactors, (1 : ℝ)) ≤
          ∏ k ∈ Finset.Icc 2 d \ d.primeFactors, ((k : ℝ) ^ 2 / ((k : ℝ) ^ 2 - 1)) :=
        Finset.prod_le_prod (fun k _ ↦ zero_le_one)
          fun k hk ↦ hfge1 k (Finset.mem_sdiff.mp hk).1
      simpa using h1
    nlinarith [hprimenn]
  rcases Nat.lt_or_ge d 2 with hlt | hge
  · interval_cases d
    · simp
  · rw [Finset.prod_Icc_sq_div_sq_sub_one d hge] at hle
    refine hle.trans ?_
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (d : ℝ) + 1)]
    linarith

end Nat

namespace PrimeGaps

open ArithmeticFunction
open PrimeGaps.MertensShared
open scoped ArithmeticFunction

/-- `hAux W` is norm-summable. -/
theorem hAux_summable_norm (W : ℕ) : Summable fun d : ℕ ↦ ‖hAux W d‖ := by
  classical
  have hdom : Summable fun d : ℕ ↦ 2 * (1 / (d : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le (fun d ↦ norm_nonneg _) (fun d ↦ ?_) hdom
  unfold hAux
  by_cases hco : Nat.Coprime d W
  · rw [if_pos hco, Real.norm_eq_abs]
    by_cases hd : Squarefree d
    · have hprodnn : (0 : ℝ) ≤ ∏ p ∈ d.primeFactors, (1 / ((p : ℝ) ^ 2 - 1)) :=
        Finset.prod_nonneg fun p hp ↦ (one_div_pos.mpr
          (cast_sq_sub_one_pos (Nat.prime_of_mem_primeFactors hp).two_le)).le
      have hpeq : (∏ p ∈ d.primeFactors, (1 / ((p : ℝ) ^ 2 - 1))) =
          (1 / (d : ℝ) ^ 2) * ∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1)) := by
        rw [cast_sq_eq_prod_primeFactors hd, one_div, ← Finset.prod_inv_distrib,
          ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl fun p hp ↦ ?_
        have hden : (p : ℝ) ^ 2 - 1 ≠ 0 :=
          (cast_sq_sub_one_pos (Nat.prime_of_mem_primeFactors hp).two_le).ne'
        have hp0 : (p : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).pos.ne'
        field_simp
      rw [cast_moebius_sq hd, one_mul, abs_of_nonneg hprodnn, hpeq]
      calc (1 / (d : ℝ) ^ 2) * ∏ p ∈ d.primeFactors, ((p : ℝ) ^ 2 / ((p : ℝ) ^ 2 - 1))
          ≤ (1 / (d : ℝ) ^ 2) * 2 :=
            mul_le_mul_of_nonneg_left
              (Nat.prod_primeFactors_sq_div_sq_sub_one_le_two hd.ne_zero) (by positivity)
        _ = 2 * (1 / (d : ℝ) ^ 2) := by ring
    · rw [show (μ d : ℝ) = 0 by exact_mod_cast moebius_eq_zero_of_not_squarefree hd]
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul, abs_zero]
      positivity
  · rw [if_neg hco]
    simp only [norm_zero]
    positivity

/-- Local Euler factor of `hAux W` at a prime `p`:
`∑' e, hAux W (p^e) = if p ∣ W then 1 else 1 + 1/(p²-1)`. -/
theorem hAux_local_factor (W : ℕ) (p : Nat.Primes) :
    (∑' e : ℕ, hAux W ((p : ℕ) ^ e)) = if (p : ℕ) ∣ W then 1 else (1 + 1 / ((p : ℝ) ^ 2 - 1)) := by
  classical
  have hp : (p : ℕ).Prime := p.prop
  have hvanish : ∀ e, 2 ≤ e → hAux W ((p : ℕ) ^ e) = 0 := by
    intro e he2
    have hμ0 : μ ((p : ℕ) ^ e) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega)]
      simp [show e ≠ 1 by omega]
    unfold hAux
    split
    · rw [hμ0]; push_cast; ring
    · rfl
  rw [tsum_ppow_eq_sum_range _ _ 2 hvanish, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : hAux W ((p : ℕ) ^ 0) = 1 := by simpa using hAux_one W
  rw [h0, pow_one]
  by_cases hdvd : (p : ℕ) ∣ W
  · rw [if_pos hdvd]
    unfold hAux
    rw [if_neg fun hc ↦ hp.coprime_iff_not_dvd.mp hc hdvd]; ring
  · rw [if_neg hdvd]
    unfold hAux
    rw [if_pos (hp.coprime_iff_not_dvd.mpr hdvd), moebius_apply_prime hp, hp.primeFactors,
      Finset.prod_singleton]
    push_cast
    ring

/-- The `hAux` Euler product. -/
theorem hAux_euler (W : ℕ) : (∑' d : ℕ, hAux W d) =
      ∏' p : Nat.Primes, if (p : ℕ) ∣ W then 1 else (1 + 1 / ((p : ℝ) ^ 2 - 1)) :=
  (EulerProduct.eulerProduct_tprod (hAux_one W) (fun {_ _} h ↦ hAux_mul_of_coprime W h)
    (hAux_summable_norm W) (hAux_zero W)).symm.trans (tprod_congr fun p ↦ hAux_local_factor W p)

private theorem multipliable_of_local_factor {F : ℕ → ℝ} (h1 : F 1 = 1)
    (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → F (m * n) = F m * F n)
    (hsum : Summable fun n : ℕ ↦ ‖F n‖) (h0 : F 0 = 0) {G : Nat.Primes → ℝ}
    (hG : ∀ p : Nat.Primes, (∑' e : ℕ, F ((p : ℕ) ^ e)) = G p) : Multipliable G := by
  have h := (EulerProduct.eulerProduct_hasProd h1 hmul hsum h0).multipliable
  rwa [funext hG] at h

/-- The leading-coefficient sum evaluates to `1`: for every squarefree `W`,
`∑' d, (if Coprime d W then μ(d)²/d² · A(dW) else 0) = 1`. -/
@[pg_tag "bg246" "slem_mertens_W_leading_coeff"]
theorem main_thm (W : ℕ) : ∑' d : ℕ, (if Nat.Coprime d W then
        ((μ d : ℝ) ^ 2 / (d : ℝ) ^ 2) * A (d * W)
      else 0) = 1 := by
  rw [main_thm_lhs_eq, tsum_congr fun d ↦ outerTerm_eq_const_mul_hAux W d, tsum_mul_left,
    hAux_euler W, A_eq_prod W]
  have hmW : Multipliable
      fun p : Nat.Primes ↦ if (p : ℕ) ∣ W then (1 : ℝ) else (1 - 1 / (p : ℝ) ^ 2) :=
    multipliable_of_local_factor (ASummand_one W) (fun {_ _} h ↦ ASummand_mul_of_coprime W h)
      (ASummand_summable_norm W) (ASummand_zero W) (ASummand_local_factor W)
  have hmA : Multipliable
      fun p : Nat.Primes ↦ if (p : ℕ) ∣ W then (1 : ℝ) else (1 + 1 / ((p : ℝ) ^ 2 - 1)) :=
    multipliable_of_local_factor (hAux_one W) (fun {_ _} h ↦ hAux_mul_of_coprime W h)
      (hAux_summable_norm W) (hAux_zero W) (hAux_local_factor W)
  rw [mul_comm, ← Multipliable.tprod_mul hmA hmW]
  have hone : (fun p : Nat.Primes ↦ (if (p : ℕ) ∣ W then (1 : ℝ) else (1 + 1 / ((p : ℝ) ^ 2 - 1))) *
        (if (p : ℕ) ∣ W then (1 : ℝ) else (1 - 1 / (p : ℝ) ^ 2))) =
      fun _ : Nat.Primes ↦ (1 : ℝ) := by
    funext p
    by_cases hdvd : (p : ℕ) ∣ W
    · simp [hdvd]
    · simp only [hdvd, if_false]
      rw [mul_comm]
      exact local_combine (p : ℕ) p.prop.one_lt
  rw [hone, tprod_one]

end PrimeGaps
