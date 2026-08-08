/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Complex.ExponentialBounds
public import PrimeGapsTheory.NumberTheory.PrimeSumEstimates
public import PrimeGapsTheory.Arithmetic.Totient.Lcm

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Mertens estimates for the divisor function

Bounds for weighted sums involving the `k`-fold divisor function.

## Main definitions

* `weightedSum`: The Möbius- and totient-weighted divisor sum.

## Main results

* `weightedSum_le`: A logarithmic upper bound for the weighted divisor sum.
-/

@[expose] public section

open Real

open scoped Topology
open scoped Interval

open ArithmeticFunction Finset

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta ArithmeticFunction

namespace WeightedDivisorSum

/-- The real-valued weighted partial sum
`∑_{1 ≤ u ≤ z} μ(u)^2 τ_k(u) / φ(u)`. Here `⌊z⌋₊` is the floor of `z`, so the
sum ranges over positive integers `u` with `1 ≤ u ≤ z`. -/
noncomputable def weightedSum (k : ℕ) (z : ℝ) : ℝ :=
  ∑ u ∈ Finset.Icc 1 ⌊z⌋₊,
    ((μ u) ^ 2 * ((ζ ^ k) u) : ℝ) / (Nat.totient u : ℝ)

/-- `τ_1` is the constant-one function `ζ`. -/
theorem tau_one : (ζ ^ 1) = ζ := pow_one _

/-- The Dirichlet recurrence: `τ_{r+1} = τ_r * ζ`, i.e.
`τ_{r+1}(n) = ∑_{d ∣ n} τ_r(d)` for `n ≠ 0`. -/
theorem tau_succ (r : ℕ) : (ζ ^ (r + 1)) = (ζ ^ r) * ζ := pow_succ _ _

/-- The explicit divisor-sum form of the recurrence. -/
theorem tau_succ_apply (r n : ℕ) : (ζ ^ (r + 1)) n = ∑ d ∈ n.divisors, (ζ ^ r) d := by
  rw [tau_succ]
  exact ArithmeticFunction.coe_mul_zeta_apply

/-- For `n ≠ 0`, `τ_1(n) = 1`. -/
theorem tau_one_apply {n : ℕ} (hn : n ≠ 0) : (ζ ^ 1) n = 1 := by
  simp [ArithmeticFunction.zeta_apply, hn]

/-- **Lemma A (Euler-product upper bound).** The weighted sum over `u ≤ z` is
bounded by the finite Euler product over the primes `p ≤ z`. -/
theorem weightedSum_le_prod (k : ℕ) (z : ℝ) : weightedSum k z ≤
      ∏ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 + (k : ℝ) / (p - 1)) := by
  have tm : ∀ j, ((ζ ^ j)).IsMultiplicative :=
    fun _ ↦ ArithmeticFunction.isMultiplicative_zeta.pow
  have tau_mult : ((ζ ^ k)).IsMultiplicative := tm k
  have tau_prime : ∀ {p : ℕ}, p.Prime → (ζ ^ k) p = k := by
    intro p hp
    induction k with
    | zero => simp [hp.ne_one]
    | succ n ih =>
      rw [tau_succ_apply, hp.divisors, Finset.sum_insert (by simp [Ne.symm hp.ne_one]),
          Finset.sum_singleton, ih (tm n), (tm n).map_one]; ring
  set F : ArithmeticFunction ℝ := {
    toFun := fun u ↦ ((μ u) ^ 2 * ((ζ ^ k) u) : ℝ) / (Nat.totient u : ℝ)
    map_zero' := by simp }
  have F_apply : ∀ u : ℕ,
      F u = ((μ u) ^ 2 * ((ζ ^ k) u) : ℝ) / (Nat.totient u : ℝ) :=
    fun u ↦ rfl
  have F_mult : F.IsMultiplicative := by
    rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
    refine ⟨?_, ?_⟩
    · rw [F_apply]; simp [tau_mult.map_one]
    · intro m n hm hn hmn
      rw [F_apply, F_apply, F_apply]
      have hμ : (μ (m * n) : ℝ) =
          μ m * μ n := by
        have := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hmn
        exact_mod_cast this
      have hτ : (((ζ ^ k) (m * n)) : ℝ) = ((ζ ^ k) m : ℝ) * ((ζ ^ k) n : ℝ) := by
        have := tau_mult.map_mul_of_coprime hmn; exact_mod_cast this
      have hφ : ((Nat.totient (m * n)) : ℝ) = (Nat.totient m : ℝ) * (Nat.totient n : ℝ) := by
        rw [Nat.totient_mul hmn]; push_cast; ring
      rw [hμ, hτ, hφ]
      have hφm : (Nat.totient m : ℝ) ≠ 0 := by
        have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hm); positivity
      have hφn : (Nat.totient n : ℝ) ≠ 0 := by
        have := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hn); positivity
      field_simp
  have F_prime : ∀ {p : ℕ}, p.Prime → F p = (k : ℝ) / (p - 1) := by
    intro p hp
    rw [F_apply, tau_prime hp, ArithmeticFunction.moebius_apply_prime hp, Nat.totient_prime hp,
        Nat.cast_sub hp.one_le]
    push_cast; ring
  have F_nonneg : ∀ u : ℕ, 0 ≤ F u := by
    intro u; rw [F_apply]; apply div_nonneg <;> positivity
  have F_zero_of_not_sqfree : ∀ u : ℕ, ¬ Squarefree u → F u = 0 := by
    intro u hu
    rw [F_apply, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hu]; simp
  set N := ⌊z⌋₊ + 1
  set R := ∏ p ∈ Nat.primesBelow N, p with hR
  have hprimes : ∀ p ∈ Nat.primesBelow N, p.Prime := fun p hp ↦ Nat.prime_of_mem_primesBelow hp
  have hRsqfree : Squarefree R := Nat.squarefree_prod_of_forall_prime hprimes
  have hRpf : R.primeFactors = Nat.primesBelow N := Nat.primeFactors_prod hprimes
  have hRpos : 0 < R := Finset.prod_pos fun p hp ↦ (hprimes p hp).pos
  have key := F_mult.prodPrimeFactors_one_add_of_squarefree hRsqfree
  rw [hRpf] at key
  have hLHS : ∏ p ∈ Nat.primesBelow N, (1 + F p) =
      ∏ p ∈ Nat.primesBelow N, (1 + (k : ℝ) / (p - 1)) :=
    Finset.prod_congr rfl fun p hp ↦ by rw [F_prime (hprimes p hp)]
  rw [hLHS] at key
  rw [key]
  have hws : weightedSum k z = ∑ u ∈ Finset.Icc 1 ⌊z⌋₊, F u := rfl
  rw [hws]
  have hdvd : ∀ u ∈ Finset.Icc 1 ⌊z⌋₊, Squarefree u → u ∣ R := by
    intro u hu husf
    rw [Finset.mem_Icc] at hu
    have hsub : u.primeFactors ⊆ Nat.primesBelow N := by
      intro p hp
      rw [Nat.mem_primeFactors] at hp
      rw [Nat.mem_primesBelow]
      refine ⟨?_, hp.1⟩
      have hpu : p ≤ u := Nat.le_of_dvd (by omega) hp.2.1
      omega
    have h1 : (∏ p ∈ u.primeFactors, p) ∣ R := by
      rw [hR]; exact prod_dvd_prod_of_subset _ _ (fun i ↦ i) hsub
    rwa [Nat.prod_primeFactors_of_squarefree husf] at h1
  have hfilter : ∑ u ∈ Finset.Icc 1 ⌊z⌋₊, F u = ∑ u ∈ {u ∈ Finset.Icc 1 ⌊z⌋₊ | u ∣ R}, F u := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun u hu ↦ ?_
    by_cases hd : u ∣ R
    · rw [if_pos hd]
    · rw [if_neg hd]; exact F_zero_of_not_sqfree u fun husf ↦ hd (hdvd u hu husf)
  rw [hfilter]
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun u hu ↦ ?_) fun u _ _ ↦ F_nonneg u
  rw [Finset.mem_filter, Finset.mem_Icc] at hu
  exact Nat.mem_divisors.mpr ⟨hu.2, hRpos.ne'⟩

/-- **Lemma B (`1 + x ≤ eˣ` glue).** The finite Euler product is bounded by the
exponential of the sum of its logarithmic-scale terms. -/
theorem prod_one_add_le_exp_sum (k : ℕ) (S : Finset ℕ) (hS : ∀ p ∈ S, 2 ≤ p) :
    ∏ p ∈ S, (1 + (k : ℝ) / (p - 1)) ≤ rexp (∑ p ∈ S, (k : ℝ) / (p - 1)) := by
  rw [Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hS p hp
    have : (0 : ℝ) ≤ (k : ℝ) / (p - 1) := div_nonneg (by positivity) (by linarith)
    linarith
  · exact fun p _ ↦ by linarith [Real.add_one_le_exp ((k : ℝ) / (p - 1))]

/-- **Von Mangoldt average, coefficient exactly 1.**
`∑_{n ≤ x} Λ(n)/n ≤ log x + C₂` for an absolute constant `C₂`, all `x ≥ 2`; the
coefficient on `log x` is exactly `1`. Proved from the Mertens-type bound
`PrimeGaps.abs_sum_vonMangoldt_div_sub_log` at `N = ⌊x⌋₊`, together with
`log ⌊x⌋₊ ≤ log x`. -/
theorem sum_vonMangoldt_div_le : ∃ C₂ : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / n ≤ Real.log x + C₂ := by
  refine ⟨Real.log 4 + 5, ?_⟩
  intro x hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hN1 : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1 : ℝ) ≤ x))
  have hNpos : (0 : ℝ) < (⌊x⌋₊ : ℝ) := by exact_mod_cast hN1
  have hkey := PrimeGaps.abs_sum_vonMangoldt_div_sub_log hN1
  rw [abs_le] at hkey
  have hfloor : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le (le_of_lt hxpos)
  linarith [hkey.2, Real.log_le_log hNpos hfloor]

/-- **Drop prime powers.** `∑_{p ≤ x} (log p)/p ≤ log x + C₃` for `x ≥ 2`.
Since `Λ(p) = log p` on primes and `Λ(n)/n ≥ 0`, the prime sum is dominated by the
full von Mangoldt average `∑_{n ≤ x} Λ(n)/n` (`sum_vonMangoldt_div_le`) via
`Finset.sum_le_sum_of_subset_of_nonneg`, so one may take `C₃ = C₂`. -/
theorem sum_log_div_prime_le : ∃ C₃ : ℝ, ∀ x : ℝ, 2 ≤ x →
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p ≤ Real.log x + C₃ := by
  obtain ⟨C₂, hC₂⟩ := sum_vonMangoldt_div_le
  refine ⟨C₂, fun x hx ↦ ?_⟩
  have hrw : ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p =
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Λ p / p :=
    Finset.sum_congr rfl fun p hp ↦ by
      rw [ArithmeticFunction.vonMangoldt_apply_prime (Nat.prime_of_mem_primesBelow hp)]
  rw [hrw]
  have hsub : Nat.primesBelow (⌊x⌋₊ + 1) ⊆ Finset.Ioc 0 ⌊x⌋₊ := fun p hp ↦ by
    rw [Nat.mem_primesBelow] at hp
    exact Finset.mem_Ioc.mpr ⟨hp.2.pos, Nat.lt_succ_iff.mp hp.1⟩
  have hnonneg : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      n ∉ Nat.primesBelow (⌊x⌋₊ + 1) → 0 ≤ Λ n / n :=
    fun n _ _ ↦ div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n)
  calc ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Λ p / p
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, Λ n / n :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
    _ ≤ Real.log x + C₂ := hC₂ x hx

/-- A globally differentiable extension of `t ↦ (log t)⁻¹`: it agrees with `(log t)⁻¹` on
`[2, ∞)` and is continued below `2` by the tangent line at `2`. -/
private noncomputable def invLogExt (t : ℝ) : ℝ :=
  if t ≤ 2 then (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2) else (Real.log t)⁻¹

/-- The derivative of `invLogExt`: `-(t (log t)²)⁻¹` read at `max t 2`, so it is
`-(t (log t)²)⁻¹` above `2` and constant below. -/
private noncomputable def invLogExtDeriv (t : ℝ) : ℝ :=
  -(max t 2 * (Real.log (max t 2)) ^ 2)⁻¹

/-- `invLogExt` agrees with `(log t)⁻¹` on `[2, ∞)`. -/
private lemma invLogExt_eq_inv_log {t : ℝ} (ht : 2 ≤ t) : invLogExt t = (Real.log t)⁻¹ := by
  rcases eq_or_lt_of_le ht with h | h
  · simp only [invLogExt]; rw [if_pos (le_of_eq h.symm), ← h]; ring
  · simp only [invLogExt]; rw [if_neg (by linarith)]

/-- Above `2`, `invLogExtDeriv t` is `-(t (log t)²)⁻¹`. -/
private lemma invLogExtDeriv_of_two_lt {t : ℝ} (ht : 2 < t) :
    invLogExtDeriv t = -(t * (Real.log t) ^ 2)⁻¹ := by
  rw [invLogExtDeriv, max_eq_left ht.le]

/-- `t ↦ (log t)⁻¹` has derivative `-(t (log t)²)⁻¹` at every `t > 1`. -/
private lemma hasDerivAt_inv_log {t : ℝ} (ht : 1 < t) :
    HasDerivAt (fun s ↦ (Real.log s)⁻¹) (-(t * (Real.log t) ^ 2)⁻¹) t := by
  refine (Real.hasDerivAt_inv_log (by linarith : (0 : ℝ) < t).ne' ht.ne'
    (by linarith : (-1 : ℝ) < t).ne').congr_deriv ?_
  rw [neg_div, neg_inj, div_eq_mul_inv, mul_inv_rev, mul_comm]

/-- `invLogExtDeriv` is continuous: `max t 2` stays above `2`, where the logarithm is positive and
the denominator therefore nonzero. -/
private lemma continuous_invLogExtDeriv : Continuous invLogExtDeriv := by
  have hmax : ∀ t : ℝ, (2 : ℝ) ≤ max t 2 := fun t ↦ le_max_right _ _
  have hm : Continuous fun t : ℝ ↦ max t 2 := continuous_id.max continuous_const
  have hlog : Continuous fun t : ℝ ↦ Real.log (max t 2) :=
    hm.log fun t ↦ by linarith [hmax t]
  refine ((hm.mul (hlog.pow 2)).inv₀ fun t ↦ ?_).neg
  have hpos : 0 < Real.log (max t 2) := Real.log_pos (by linarith [hmax t])
  exact (mul_pos (by linarith [hmax t]) (pow_pos hpos 2)).ne'

/-- `invLogExt` is differentiable on all of `ℝ`, with derivative `invLogExtDeriv`. -/
private lemma hasDerivAt_invLogExt (y : ℝ) : HasDerivAt invLogExt (invLogExtDeriv y) y := by
  have hl2 : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hne : ∀ y : ℝ, y ≠ 2 → HasDerivAt invLogExt (invLogExtDeriv y) y := by
    intro y hy
    rcases lt_or_gt_of_ne hy with hlt | hgt
    · have hda : HasDerivAt (fun t ↦ (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2))
          (-(2 * (Real.log 2) ^ 2)⁻¹) y := by
        have := ((hasDerivAt_id y).sub_const (2 : ℝ)).const_mul (-(2 * (Real.log 2) ^ 2)⁻¹)
        simpa using (this.const_add ((Real.log 2)⁻¹))
      have heq : invLogExt =ᶠ[𝓝 y]
          (fun t ↦ (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2)) := by
        filter_upwards [eventually_lt_nhds hlt] with t ht
        simp only [invLogExt]; rw [if_pos (le_of_lt ht)]
      rw [invLogExtDeriv, max_eq_right hlt.le]
      exact hda.congr_of_eventuallyEq heq
    · have hd := hasDerivAt_inv_log (t := y) (by linarith)
      have heq : invLogExt =ᶠ[𝓝 y] (fun s ↦ (Real.log s)⁻¹) := by
        filter_upwards [eventually_gt_nhds hgt] with t ht
        simp only [invLogExt]; rw [if_neg (by linarith)]
      rw [invLogExtDeriv, max_eq_left hgt.le]
      exact hd.congr_of_eventuallyEq heq
  rcases eq_or_ne y 2 with rfl | hy
  · apply hasDerivAt_of_hasDerivAt_of_ne (fun z hz ↦ hne z hz)
    · have hcont_le : ContinuousWithinAt invLogExt (Set.Iic 2) 2 := by
        apply ContinuousWithinAt.congr
          (f := fun t ↦ (Real.log 2)⁻¹ + (-(2 * (Real.log 2) ^ 2)⁻¹) * (t - 2))
        · fun_prop
        · intro t ht; simp only [invLogExt]; rw [if_pos (Set.mem_Iic.mp ht)]
        · simp only [invLogExt]; rw [if_pos le_rfl]
      have hcont_ge : ContinuousWithinAt invLogExt (Set.Ici 2) 2 := by
        apply ContinuousWithinAt.congr (f := fun t ↦ (Real.log t)⁻¹)
        · exact ((Real.continuousAt_log (by norm_num)).continuousWithinAt).inv₀ hl2
        · intro t ht; exact invLogExt_eq_inv_log (Set.mem_Ici.mp ht)
        · simp only [invLogExt]; rw [if_pos le_rfl]; ring
      have hu : ContinuousWithinAt invLogExt (Set.Iic 2 ∪ Set.Ici 2) 2 := hcont_le.union hcont_ge
      rwa [Set.Iic_union_Ici, continuousWithinAt_univ] at hu
    · exact continuous_invLogExtDeriv.continuousAt
  · exact hne y hy

/-- **Abel/partial summation identity.** For `x ≥ e`, with partial sums
`A(t) = ∑_{p ≤ t} (log p)/p`, the inverse-prime sum is recovered by partial summation
against the C¹ weight `f(t) = 1/log t`:
  `∑_{p ≤ x} 1/p = A(x)/log x + ∫₂ˣ A(t)/(t (log t)²) dt`.
This applies `sum_mul_eq_sub_integral_mul` (`Mathlib.NumberTheory.AbelSummation`) with
weight `c k = if k.Prime then (log k)/k else 0`. Since `1/log t` is not differentiable
at `t ∈ {0, 1}`, it is replaced by a function `g` agreeing with `1/log t` on `[2, ∞)`
and differentiable on all of `[0, x]`; this is harmless because `A(t) = 0` for `t < 2`,
so the integrand vanishes where `g` and `1/log t` differ. -/
theorem abel_sum_inv_prime : ∀ x : ℝ, rexp 1 ≤ x →
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p =
        (∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p) / Real.log x + ∫ t in Set.Ioc (2 : ℝ) x,
              (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2) := by
  intro x hx
  have he2 : (2 : ℝ) < rexp 1 := by have := Real.exp_one_gt_d9; linarith
  have hx2 : (2 : ℝ) ≤ x := he2.le.trans hx
  have hxgt2 : (2 : ℝ) < x := he2.trans_le hx
  set g : ℝ → ℝ := invLogExt
  set dg : ℝ → ℝ := invLogExtDeriv
  set c : ℕ → ℝ := fun k ↦ if k.Prime then Real.log k / k else 0 with hcdef
  have hg_eq : ∀ t : ℝ, 2 ≤ t → g t = (Real.log t)⁻¹ := fun _ ht ↦ invLogExt_eq_inv_log ht
  have g_hasDeriv : ∀ y : ℝ, HasDerivAt g (dg y) y := hasDerivAt_invLogExt
  have hderiv_g : ∀ y, deriv g y = dg y := fun y ↦ (g_hasDeriv y).deriv
  have dg_cont : Continuous dg := continuous_invLogExtDeriv
  have hf' : MeasureTheory.IntegrableOn (deriv g) (Set.Icc 0 x) MeasureTheory.volume := by
    have hdgeq : deriv g = dg := funext hderiv_g
    rw [hdgeq]
    exact (dg_cont.continuousOn).integrableOn_compact isCompact_Icc
  have hf : ∀ t ∈ Set.Icc (0 : ℝ) x, DifferentiableAt ℝ g t :=
    fun t _ ↦ (g_hasDeriv t).differentiableAt
  have hb : (0 : ℝ) ≤ x := by linarith
  have habel := sum_mul_eq_sub_integral_mul c hb hf hf'
  have recon : ∀ (m : ℕ) (v : ℕ → ℝ),
      ∑ k ∈ Finset.Icc 0 m, (if k.Prime then v k else 0) = ∑ p ∈ Nat.primesBelow (m + 1), v p := by
    intro m v
    rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
    apply Finset.sum_congr _ (fun _ _ ↦ rfl)
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow]
    exact ⟨fun h ↦ ⟨by omega, h.2⟩, fun h ↦ ⟨⟨Nat.zero_le _, by omega⟩, h.2⟩⟩
  have hAdisc : ∀ t : ℝ, (∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
      ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p :=
    fun t ↦ by rw [hcdef]; exact recon ⌊t⌋₊ fun k ↦ Real.log k / k
  have hLHS : ∑ k ∈ Finset.Icc 0 ⌊x⌋₊, g ↑k * c k =
      ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), (1 : ℝ) / p := by
    rw [← recon ⌊x⌋₊ (fun k ↦ (1 : ℝ) / k)]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [hcdef]; simp only
    by_cases hp : k.Prime
    · rw [if_pos hp, if_pos hp]
      have hk2 : 2 ≤ k := hp.two_le
      have hkr : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk2
      rw [hg_eq k hkr]
      have hlogk : Real.log k ≠ 0 :=
        (Real.log_pos (by exact_mod_cast hp.one_lt : (1 : ℝ) < (k : ℝ))).ne'
      field_simp
    · rw [if_neg hp, if_neg hp, mul_zero]
  have hgx : g x = (Real.log x)⁻¹ := hg_eq x hx2
  have hInt : (∫ (t : ℝ) in Set.Ioc 0 x, deriv g t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) = -
      ∫ t in Set.Ioc (2 : ℝ) x,
          (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2) := by
    have hrw : (∫ (t : ℝ) in Set.Ioc 0 x, deriv g t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, c k) =
        ∫ (t : ℝ) in Set.Ioc 0 x, dg t * (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) := by
      apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
      intro t _; dsimp only; rw [hderiv_g, hAdisc t]
    rw [hrw]
    set A : ℝ → ℝ := fun t ↦ ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p with hAdef
    have hA0 : ∀ t, t < 2 → A t = 0 := by
      intro t ht
      rw [hAdef]; simp only
      apply Finset.sum_eq_zero
      intro p hp
      rw [Nat.mem_primesBelow] at hp
      have hfloor : ⌊t⌋₊ ≤ 1 := by
        rcases lt_or_ge t 0 with h0 | h0
        · rw [Nat.floor_eq_zero.mpr (by linarith)]; omega
        · have := (Nat.floor_lt h0).mpr (by exact_mod_cast ht : t < ((2 : ℕ) : ℝ)); omega
      exact absurd hp.2.two_le (by omega)
    have hdg : ∀ t, 2 < t → dg t = -(t * (Real.log t) ^ 2)⁻¹ :=
      fun _ ht ↦ invLogExtDeriv_of_two_lt ht
    have hinter : Set.Ioc (0 : ℝ) x ∩ Set.Ioc (2 : ℝ) x = Set.Ioc (2 : ℝ) x := by
      rw [Set.inter_eq_right]; intro t ht; rw [Set.mem_Ioc] at ht ⊢; exact ⟨by linarith, ht.2⟩
    have step1 : (∫ t in Set.Ioc (0 : ℝ) x, dg t * A t) = ∫ t in Set.Ioc (0 : ℝ) x,
          (Set.Ioc (2 : ℝ) x).indicator (fun t ↦ -(A t / (t * (Real.log t) ^ 2))) t := by
      apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
      have hne : ∀ᵐ t ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ), t ≠ 2 := by
        rw [MeasureTheory.ae_iff]; simp
      filter_upwards [hne] with t htne hmem
      rw [Set.mem_Ioc] at hmem
      rcases lt_trichotomy t 2 with hlt | heq | hgt
      · rw [hA0 t hlt, mul_zero, Set.indicator_of_notMem]
        rw [Set.mem_Ioc]; rintro ⟨h, _⟩; linarith
      · exact absurd heq htne
      · rw [Set.indicator_of_mem (by rw [Set.mem_Ioc]; exact ⟨hgt, hmem.2⟩), hdg t hgt]
        field_simp
    rw [step1, MeasureTheory.setIntegral_indicator measurableSet_Ioc, hinter,
      MeasureTheory.integral_neg]
  rw [hLHS] at habel
  rw [habel, hgx, hInt, hAdisc x]
  ring

/-- On `[2, x]` the function `t ↦ k / (t (log t)ⁿ)` is continuous: the denominator is a product
of continuous factors and is bounded away from `0`, since `t ≥ 2` gives `log t > 0`. -/
private lemma continuousOn_const_div_mul_log_pow (k : ℝ) (n : ℕ) {x : ℝ} (hx2 : (2 : ℝ) ≤ x) :
    ContinuousOn (fun t ↦ k / (t * (Real.log t) ^ n)) ([[2, x]]) := by
  rw [Set.uIcc_of_le hx2]
  apply ContinuousOn.div continuousOn_const
  · apply continuousOn_id.mul
    apply ContinuousOn.pow
    exact (Real.continuousOn_log.mono (by
      intro t ht; simp only [Set.mem_Icc] at ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]; linarith [ht.1]))
  · intro t ht
    simp only [Set.mem_Icc] at ht
    have h1 : (0 : ℝ) < t := by linarith [ht.1]
    have h2 : (0 : ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
    positivity

/-- **Integral bound via the antiderivative `log log t`.** Using `A(t) ≤ log t + C₃`
(from `sum_log_div_prime_le`) and the antiderivatives `d/dt log log t = 1/(t log t)`
and `d/dt (-1/log t) = 1/(t (log t)²)`, the Abel integral of `A(t)/(t (log t)²)` over
`[2, x]` is bounded by `log log x` plus an absolute constant `C₄`, for `x ≥ e`:
  `∫_2^x A(t)/(t (log t)²) dt ≤ ∫_2^x (log t + C₃)/(t (log t)²) dt
     = (log log x - log log 2) + C₃ (1/log 2 - 1/log x)
     ≤ log log x + C₄`.
The two explicit integrals are evaluated by the Fundamental Theorem of Calculus; the
constant `C₄` is chosen existentially. -/
theorem abel_integral_bound (C₃ : ℝ)
    (hC₃ : ∀ x : ℝ, 2 ≤ x → ∑ p ∈ Nat.primesBelow (⌊x⌋₊ + 1), Real.log p / p ≤ Real.log x + C₃) :
    ∃ C₄ : ℝ, ∀ x : ℝ, rexp 1 ≤ x → (∫ t in Set.Ioc (2 : ℝ) x,
          (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2)) ≤
        Real.log (Real.log x) + C₄ := by
  set A : ℝ → ℝ := fun t ↦ ∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p
  have hAmeas : Measurable A := by
    have : A = (fun n : ℕ ↦ ∑ p ∈ Nat.primesBelow (n + 1), Real.log p / p) ∘ (fun t : ℝ ↦ ⌊t⌋₊) :=
      rfl
    rw [this]
    exact (measurable_from_nat).comp Nat.measurable_floor
  refine ⟨(max C₃ 0) / Real.log 2 - Real.log (Real.log 2), ?_⟩
  intro x hx
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h2e : (2 : ℝ) ≤ rexp 1 := by
    have := Real.add_one_le_exp (1 : ℝ); linarith
  have hx2 : (2 : ℝ) ≤ x := le_trans h2e hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx1 : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (by positivity) hx
  have hlogxpos : (0 : ℝ) < Real.log x := by linarith
  set g : ℝ → ℝ := fun t ↦ 1 / (t * Real.log t) + C₃ / (t * (Real.log t) ^ 2) with hg
  have huicc : [[(2 : ℝ), x]] = Set.Icc 2 x := Set.uIcc_of_le hx2
  have hcont1 : ContinuousOn (fun t ↦ 1 / (t * Real.log t)) ([[2, x]]) := by
    simpa only [pow_one] using continuousOn_const_div_mul_log_pow 1 1 hx2
  have hcont2 : ContinuousOn (fun t ↦ C₃ / (t * (Real.log t) ^ 2)) ([[2, x]]) :=
    continuousOn_const_div_mul_log_pow C₃ 2 hx2
  have hgcont : ContinuousOn g ([[2, x]]) := hcont1.add hcont2
  have hgint : IntervalIntegrable g MeasureTheory.volume 2 x := hgcont.intervalIntegrable
  set f : ℝ → ℝ := fun t ↦ A t / (t * (Real.log t) ^ 2) with hf
  have hfmeas : Measurable f :=
    hAmeas.div (measurable_id.mul ((Real.measurable_log.comp measurable_id).pow_const 2))
  have hbound : ∀ t ∈ Set.Icc (2 : ℝ) x, f t ≤ g t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have hlt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
    have hAle : A t ≤ Real.log t + C₃ := hC₃ t ht.1
    change A t / (t * (Real.log t) ^ 2) ≤ 1 / (t * Real.log t) + C₃ / (t * (Real.log t) ^ 2)
    have hden : (0 : ℝ) < t * (Real.log t) ^ 2 := by positivity
    have e1 : 1 / (t * Real.log t) = Real.log t / (t * (Real.log t) ^ 2) := by field_simp
    rw [e1, ← add_div, div_le_div_iff_of_pos_right hden]
    linarith
  have hfnonneg : ∀ t ∈ Set.Icc (2 : ℝ) x, 0 ≤ f t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0 : ℝ) < t := by linarith [ht.1]
    have hlt : (0 : ℝ) < Real.log t := Real.log_pos (by linarith [ht.1])
    have hAn : 0 ≤ A t := Finset.sum_nonneg fun p hp ↦ by
      have : (0 : ℝ) ≤ Real.log p :=
        Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le)
      positivity
    change 0 ≤ A t / (t * (Real.log t) ^ 2)
    positivity
  have hfint : IntervalIntegrable f MeasureTheory.volume 2 x := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx2]
    have hginton : MeasureTheory.IntegrableOn g (Set.Ioc 2 x) MeasureTheory.volume := by
      rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hx2]; exact hgint
    refine (hginton.mono' hfmeas.aestronglyMeasurable ?_)
    refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc fun t ht ↦ ?_
    rw [Set.mem_Ioc] at ht
    have htmem : t ∈ Set.Icc (2 : ℝ) x := Set.mem_Icc.mpr ⟨ht.1.le, ht.2⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hfnonneg t htmem)]
    exact hbound t htmem
  rw [← intervalIntegral.integral_of_le hx2]
  calc ∫ t in (2 : ℝ)..x, f t
      ≤ ∫ t in (2 : ℝ)..x, g t := intervalIntegral.integral_mono_on hx2 hfint hgint hbound
    _ = (Real.log (Real.log x) - Real.log (Real.log 2)) +
          C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) := by
        rw [hg]
        rw [intervalIntegral.integral_add hcont1.intervalIntegrable hcont2.intervalIntegrable]
        congr 1
        · have hderiv : ∀ t ∈ [[(2 : ℝ), x]],
              HasDerivAt (fun s ↦ Real.log (Real.log s)) (1 / (t * Real.log t)) t := by
            intro t ht
            rw [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
            have htne : t ≠ 0 := by linarith [ht.1]
            have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
            refine (Real.hasDerivAt_log_log htne (by linarith [ht.1] : (1 : ℝ) < t).ne'
              (by linarith [ht.1] : (-1 : ℝ) < t).ne').congr_deriv ?_
            field_simp
          rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont1.intervalIntegrable]
        · have hderiv : ∀ t ∈ [[(2 : ℝ), x]],
              HasDerivAt (fun s ↦ -(Real.log s)⁻¹) (1 / (t * (Real.log t) ^ 2)) t := by
            intro t ht
            rw [Set.uIcc_of_le hx2, Set.mem_Icc] at ht
            have htne : t ≠ 0 := by linarith [ht.1]
            have hlt : Real.log t ≠ 0 := ne_of_gt (Real.log_pos (by linarith [ht.1]))
            have h2 := Real.hasDerivAt_inv_log htne (by linarith [ht.1] : t ≠ 1)
              (by linarith [ht.1] : t ≠ -1)
            refine h2.neg.congr_deriv ?_
            rw [neg_div, neg_neg]
            field_simp [htne, pow_ne_zero 2 hlt]
          have hcont2' : ContinuousOn (fun t ↦ 1 / (t * (Real.log t) ^ 2)) ([[2, x]]) :=
            continuousOn_const_div_mul_log_pow 1 2 hx2
          have key : ∫ t in (2 : ℝ)..x, 1 / (t * (Real.log t) ^ 2) =
              (Real.log 2)⁻¹ - (Real.log x)⁻¹ := by
            rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
              hcont2'.intervalIntegrable]; ring
          rw [show (fun t ↦ C₃ / (t * (Real.log t) ^ 2)) =
            (fun t ↦ C₃ * (1 / (t * (Real.log t) ^ 2))) from by funext t; ring]
          rw [intervalIntegral.integral_const_mul, key]
    _ ≤ Real.log (Real.log x) + (max C₃ 0 / Real.log 2 - Real.log (Real.log 2)) := by
        have hxinv : (0 : ℝ) < (Real.log x)⁻¹ := by positivity
        have hdiff : (Real.log 2)⁻¹ - (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ := by linarith
        have hdiffpos : (0 : ℝ) ≤ (Real.log 2)⁻¹ - (Real.log x)⁻¹ := by
          have hle : (Real.log x)⁻¹ ≤ (Real.log 2)⁻¹ := by
            have hlog2x : Real.log 2 ≤ Real.log x := by
              apply Real.log_le_log (by norm_num)
              exact le_trans h2e hx
            gcongr
          linarith
        have hCmax : C₃ ≤ max C₃ 0 := le_max_left _ _
        have hmaxnn : (0 : ℝ) ≤ max C₃ 0 := le_max_right _ _
        have hterm : C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) ≤ max C₃ 0 / Real.log 2 := by
          rcases lt_or_ge C₃ 0 with hC | hC
          · have hle0 : C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) ≤ 0 :=
              mul_nonpos_of_nonpos_of_nonneg (le_of_lt hC) hdiffpos
            have hge0 : (0 : ℝ) ≤ max C₃ 0 / Real.log 2 := by positivity
            linarith
          · have h1' : C₃ * ((Real.log 2)⁻¹ - (Real.log x)⁻¹) ≤ C₃ * (Real.log 2)⁻¹ :=
              mul_le_mul_of_nonneg_left hdiff hC
            have h2' : C₃ * (Real.log 2)⁻¹ ≤ max C₃ 0 * (Real.log 2)⁻¹ :=
              mul_le_mul_of_nonneg_right hCmax (le_of_lt (by positivity))
            rw [div_eq_mul_inv]; linarith
        linarith

/-- **Endpoint reconciliation for `2 ≤ z ≤ e`.** On `[2, e]` we have `⌊z⌋₊ = 2` (since
`e < 3`), so `Nat.primesBelow (⌊z⌋₊ + 1) = {2}` and the sum is exactly `1/2`. As
`log log z` is increasing and minimized at `z = 2` on this range, the bound
`∑_{p ≤ z} 1/p ≤ log log z + B₀` holds with the absolute constant
`B₀ = 1/2 - log log 2` (note `log log 2 < 0`). -/
theorem sum_inv_prime_le_endpoint : ∃ B₀ : ℝ, ∀ z : ℝ, 2 ≤ z → z ≤ rexp 1 →
      ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / p ≤ Real.log (Real.log z) + B₀ := by
  refine ⟨1 / 2 - Real.log (Real.log 2), ?_⟩
  intro z hz2 hze
  have hz3 : z < 3 := by have := Real.exp_one_lt_d9; linarith
  have hfloor : ⌊z⌋₊ = 2 := by
    rw [Nat.floor_eq_iff (by linarith)]
    exact ⟨by exact_mod_cast hz2, by push_cast; linarith⟩
  rw [hfloor]
  have hprimes : Nat.primesBelow 3 = {2} := by decide
  rw [hprimes, Finset.sum_singleton]
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogle : Real.log 2 ≤ Real.log z := Real.log_le_log (by norm_num) hz2
  have hloglog : Real.log (Real.log 2) ≤ Real.log (Real.log z) := Real.log_le_log hlog2pos hlogle
  norm_num
  linarith

/-- **Mertens' second theorem (upper bound).** `∑_{p ≤ z} 1/p ≤ log log z + B₁` for an
absolute constant `B₁`, valid for all `z ≥ 2`; the coefficient on `log log z` is exactly
`1`. For `z ≥ e` this combines the Abel identity (`abel_sum_inv_prime`) with the integral
bound (`abel_integral_bound`); the endpoint range `[2, e]` is handled by
`sum_inv_prime_le_endpoint`. -/
theorem sum_inv_prime_le : ∃ B₁ : ℝ, ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / p ≤ Real.log (Real.log z) + B₁ := by
  obtain ⟨C₃, hC₃⟩ := sum_log_div_prime_le
  obtain ⟨B₀, hB₀⟩ := sum_inv_prime_le_endpoint
  obtain ⟨C₄, hintb⟩ := abel_integral_bound C₃ hC₃
  refine ⟨max (1 + max C₃ 0 + C₄) B₀, ?_⟩
  intro z hz
  rcases le_or_gt (rexp 1) z with hze | hze
  · have hlogz : (1 : ℝ) ≤ Real.log z := by
      have : Real.log (rexp 1) ≤ Real.log z := Real.log_le_log (Real.exp_pos 1) hze
      rwa [Real.log_exp] at this
    have hAle : (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) ≤ Real.log z + C₃ :=
      hC₃ z (by linarith [Real.add_one_le_exp (1 : ℝ)] )
    have hAnn : 0 ≤ (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) :=
      Finset.sum_nonneg fun p hp ↦ by
        have : (0 : ℝ) ≤ Real.log p :=
          Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_le)
        positivity
    have hterm1 : (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) / Real.log z ≤
        1 + max C₃ 0 := by
      rw [div_le_iff₀ (by linarith)]
      have hmax : C₃ ≤ max C₃ 0 := le_max_left _ _
      have hmax0 : (0 : ℝ) ≤ max C₃ 0 := le_max_right _ _
      nlinarith [hAle, hAnn, hlogz, hmax, hmax0]
    have hident := abel_sum_inv_prime z hze
    have hintbz := hintb z hze
    rw [hident]
    calc (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), Real.log p / p) / Real.log z +
            (∫ t in Set.Ioc (2 : ℝ) z,
                  (∑ p ∈ Nat.primesBelow (⌊t⌋₊ + 1), Real.log p / p) / (t * (Real.log t) ^ 2)) ≤
          (1 + max C₃ 0) + (Real.log (Real.log z) + C₄) := add_le_add hterm1 hintbz
      _ ≤ Real.log (Real.log z) + (1 + max C₃ 0 + C₄) := by linarith
      _ ≤ Real.log (Real.log z) + max (1 + max C₃ 0 + C₄) B₀ := by
            have := le_max_left (1 + max C₃ 0 + C₄) B₀; linarith
  · have := hB₀ z hz (le_of_lt hze)
    calc ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / p ≤ Real.log (Real.log z) + B₀ := this
      _ ≤ Real.log (Real.log z) + max (1 + max C₃ 0 + C₄) B₀ := by
          have := le_max_right (1 + max C₃ 0 + C₄) B₀; linarith

/-- **Convergent correction.** `∑_{p ≤ z} 1/(p(p-1)) ≤ 1` for all `z ≥ 2`.

The primes `p ≤ z` are a subset of the integers `2 ≤ n ≤ ⌊z⌋₊`, and on integers
`n ≥ 2`, `1/(n(n-1)) = 1/(n-1) - 1/n`, which telescopes:
`∑_{n=2}^{N} 1/(n(n-1)) = 1 - 1/N ≤ 1`. Since every summand is nonnegative, the
sum over the prime subset is bounded by the full telescoping sum, i.e. by `1`
(via `Finset.sum_le_sum_of_subset_of_nonneg`). -/
theorem sum_inv_pred_mul_prime_le : ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / (p * (p - 1)) ≤ 1 := by
  have telescope : ∀ N : ℕ, 1 ≤ N → ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / (n * (n - 1)) = 1 - 1 / N := by
    intro N hN
    induction N with
    | zero => omega
    | succ m ih =>
      rcases Nat.lt_or_ge m 1 with hm | hm
      · interval_cases m; simp
      · rw [Finset.sum_Icc_succ_top (by omega), ih hm]
        have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
        have h0 : (m : ℝ) ≠ 0 := by positivity
        have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
        have hcast : (((m : ℝ) + 1) - 1) = (m : ℝ) := by ring
        push_cast
        rw [hcast]
        field_simp
        ring
  intro z hz
  set N := ⌊z⌋₊
  have hsub : Nat.primesBelow (N + 1) ⊆ Finset.Icc 2 N := fun p hp ↦ by
    rw [Nat.mem_primesBelow] at hp
    exact Finset.mem_Icc.mpr ⟨hp.2.two_le, by omega⟩
  have hnonneg : ∀ n ∈ Finset.Icc 2 N, (0 : ℝ) ≤ (1 : ℝ) / (n * (n - 1)) := by
    intro n hn
    rw [Finset.mem_Icc] at hn
    have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.1
    apply div_nonneg (by norm_num)
    nlinarith
  calc ∑ p ∈ Nat.primesBelow (N + 1), (1 : ℝ) / (p * (p - 1))
      ≤ ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) / (n * (n - 1)) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i hi _ ↦ hnonneg i hi)
    _ ≤ 1 := by
        rcases Nat.lt_or_ge N 1 with hN | hN
        · interval_cases N; simp
        · rw [telescope N hN]
          have : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
          have : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
          linarith

/-- **Mertens' theorem** in the shifted form: `∑ p < z, 1 / (p - 1) ≤ log (log z) + B` for an
absolute constant `B` and all `z ≥ 2`. -/
theorem sum_inv_pred_prime_le : ∃ B : ℝ, ∀ z : ℝ, 2 ≤ z →
      ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / (p - 1) ≤ Real.log (Real.log z) + B := by
  obtain ⟨B₁, hB₁⟩ := sum_inv_prime_le
  refine ⟨B₁ + 1, ?_⟩
  intro z hz
  have hsplit : ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / (p - 1) =
      (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / p) +
        ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / (p * (p - 1)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p hp ↦ ?_
    have hp2 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt
    have hpne : (p : ℝ) ≠ 0 := by positivity
    have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hsplit]
  have hcorr := sum_inv_pred_mul_prime_le z hz
  have hmain := hB₁ z hz
  linarith

/-- **Lemma C (Mertens kernel — the analytic core).** The exponential of
`k · ∑_{p ≤ z} 1/(p-1)` grows at most like `(log z)^k`, uniformly for `z ≥ 2`.

Now reduced (algebraically) to `sum_inv_pred_prime_le` (Lemma Cα): the only
remaining analytic content lives in that one isolated lemma. -/
theorem exp_sum_inv_pred_prime_le (k : ℕ) (hk : 1 ≤ k) : ∃ D : ℝ, 0 < D ∧ ∀ z : ℝ, 2 ≤ z →
      rexp (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (k : ℝ) / (p - 1)) ≤ D * (Real.log z) ^ k := by
  obtain ⟨B, hB⟩ := sum_inv_pred_prime_le
  refine ⟨rexp (k * B), Real.exp_pos _, ?_⟩
  intro z hz
  have hlogz : 0 < Real.log z := Real.log_pos (by linarith)
  have hsum : (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (k : ℝ) / (p - 1)) =
      (k : ℝ) * ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / (p - 1) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun p _ ↦ by ring
  rw [hsum]
  have hle : (k : ℝ) * ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / (p - 1) ≤
      (k : ℝ) * (Real.log (Real.log z) + B) :=
    mul_le_mul_of_nonneg_left (hB z hz) (by positivity)
  calc rexp ((k : ℝ) * ∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 : ℝ) / (p - 1))
      ≤ rexp ((k : ℝ) * (Real.log (Real.log z) + B)) := Real.exp_le_exp.mpr hle
    _ = rexp (k * B) * (Real.log z) ^ k := by
        have h1 : (k : ℝ) * (Real.log (Real.log z) + B) =
            (k : ℝ) * B + (k : ℝ) * Real.log (Real.log z) := by ring
        rw [h1, Real.exp_add]
        congr 1
        rw [Real.exp_nat_mul, Real.exp_log hlogz]

/-- **Bounded sum of the weighted `k`-fold divisor function.**
For every integer `k ≥ 1` there exists a constant `C_k > 0` such that for every
real `z ≥ 2`,
  `∑_{u ≤ z} μ(u)^2 τ_k(u) / φ(u) ≤ C_k (log z)^k`. -/
@[pg_tag "bg246" "lem_mertens_tau_k"]
theorem weightedSum_le (k : ℕ) (hk : 1 ≤ k) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 2 ≤ z → weightedSum k z ≤ C * (Real.log z) ^ k := by
  obtain ⟨D, hD, hDle⟩ := exp_sum_inv_pred_prime_le k hk
  refine ⟨D, hD, ?_⟩
  intro z hz
  calc weightedSum k z ≤ ∏ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (1 + (k : ℝ) / (p - 1)) :=
        weightedSum_le_prod k z
    _ ≤ rexp (∑ p ∈ Nat.primesBelow (⌊z⌋₊ + 1), (k : ℝ) / (p - 1)) :=
        prod_one_add_le_exp_sum k _ fun p hp ↦ (Nat.prime_of_mem_primesBelow hp).two_le
    _ ≤ D * (Real.log z) ^ k := hDle z hz

end WeightedDivisorSum
