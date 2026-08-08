/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.MaynardWeight
public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeHarmonic
public import PrimeGapsTheory.Arithmetic.Mertens.Shared
public import PrimeGapsTheory.Arithmetic.Totient.Basic

/-!
# The coprime-density kernel

The kernel `gKernel` and the arithmetic functions built from it.

## Main results

* `sumA_eq_conv`
-/

@[expose] public section

open PrimeGaps.MertensShared Finset ArithmeticFunction

open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

namespace PrimeGaps

/-- The squarefree `sumA` presentation equals the coprime `μ²/φ` presentation. -/
theorem sumA_eq_mobiusTotientSum (m : ℕ) (x : ℝ) : PrimeGaps.MaynardOffDiagonal.sumA m x =
      ∑ f ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun f : ℕ ↦ Nat.Coprime f m),
        ((μ f : ℝ) ^ 2) / (Nat.totient f : ℝ) := by
  unfold PrimeGaps.MaynardOffDiagonal.sumA PrimeGaps.MaynardOffDiagonal.Sset
  rw [Finset.sum_filter, Finset.sum_filter]
  refine Finset.sum_congr rfl fun f _ ↦ ?_
  by_cases hsq : Squarefree f
  · rw [show ((μ f : ℝ) ^ 2) = 1 by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq]
    by_cases hcop : Nat.Coprime f m
    · rw [if_pos ⟨hsq, hcop⟩, if_pos hcop]
    · rw [if_neg (fun h ↦ hcop h.2), if_neg hcop]
  · rw [if_neg (fun h ↦ hsq h.1), ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]
    simp

/-- The multiplicative kernel `g` arising from the Dirichlet factorisation
`μ²/φ = g ∗ (1/id)`.  Concretely `g` is the Dirichlet convolution of `f ↦ μ(f)²/φ(f)`
with the Dirichlet inverse `e ↦ μ(e)/e` of `e ↦ 1/e`:
  `g d = ∑_{a·b = d} (μ(a)²/φ(a)) · (μ(b)/b)`.
Numerically `g` is multiplicative with `g(1)=1`, `g(p)=1/(p(p-1))`, `g(p²)=-1/(p(p-1))`,
and `g(p^k)=0` for `k ≥ 3`; in particular `g` is supported on cube-free numbers and its
Euler factor `1 + g(p) + g(p²) = 1` at every prime, so `∑_{(d,m)=1} g(d) = 1`. -/
noncomputable def gKernel (d : ℕ) : ℝ :=
  ∑ ab ∈ d.divisorsAntidiagonal,
    (((μ ab.1 : ℝ) ^ 2) / (Nat.totient ab.1 : ℝ)) *
      ((μ ab.2 : ℝ) / (ab.2 : ℝ))

/-- `k(n) = μ(n)/n` packaged as an arithmetic function (the Dirichlet inverse of `1/id`). -/
noncomputable def kAF : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (μ n : ℝ) / (n : ℝ), by simp⟩

/-- `j(n) = 1/n` packaged as an arithmetic function. -/
noncomputable def jAF : ArithmeticFunction ℝ :=
  ⟨fun n ↦ 1 / (n : ℝ), by simp⟩

/-- `kAF n = μ(n)/n`. -/
@[simp] lemma kAF_apply (n : ℕ) : kAF n = (μ n : ℝ) / (n : ℝ) := rfl

/-- `jAF n = 1/n`. -/
@[simp] lemma jAF_apply (n : ℕ) : jAF n = 1 / (n : ℝ) := rfl

/-- `gKernel d = (hfun * kAF) d`, i.e. `g = (μ²/φ) ∗ (μ/id)`. -/
lemma gKernel_eq_mul (d : ℕ) : gKernel d = (hfun * kAF) d := by
  rw [ArithmeticFunction.mul_apply]; rfl

/-- `k ∗ j = 1`: `μ/id` is the Dirichlet inverse of `1/id`. -/
lemma kAF_mul_jAF : kAF * jAF = 1 := by
  ext n
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.one_apply]
  have hstep : ∀ x ∈ n.divisorsAntidiagonal,
      kAF x.1 * jAF x.2 = (μ x.1 : ℝ) * (1 / (n : ℝ)) := fun x hx ↦ by
    rw [kAF_apply, jAF_apply, ← (Nat.mem_divisorsAntidiagonal.1 hx).1]
    push_cast
    ring
  have hsum : ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ) =
      if n = 1 then 1 else 0 :=
    calc ∑ x ∈ n.divisorsAntidiagonal, (μ x.1 : ℝ)
        = ((μ : ArithmeticFunction ℝ) *
            (ζ : ArithmeticFunction ℝ)) n := by
          rw [ArithmeticFunction.mul_apply]
          exact Finset.sum_congr rfl fun x hx ↦ by
            simp [ArithmeticFunction.zeta_apply_ne
              (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hx)]
      _ = if n = 1 then 1 else 0 := by
          rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, hsum]
  by_cases h1 : n = 1 <;> simp [h1]

/-- For every `f ≥ 1`, `μ(f)²/φ(f) = ∑_{d ∣ f} g(d)/(f/d)`. -/
lemma gKernel_conv_id (f : ℕ) : ((μ f : ℝ) ^ 2) / (Nat.totient f : ℝ) =
      ∑ ab ∈ f.divisorsAntidiagonal, gKernel ab.1 * (1 / (ab.2 : ℝ)) := by
  have hrw : ∑ ab ∈ f.divisorsAntidiagonal, gKernel ab.1 * (1 / (ab.2 : ℝ)) =
      ((hfun * kAF) * jAF) f := by
    rw [ArithmeticFunction.mul_apply]
    exact Finset.sum_congr rfl fun ab _ ↦ by rw [gKernel_eq_mul, jAF_apply]
  rw [hrw, mul_assoc, kAF_mul_jAF, mul_one, hfun_apply]

/-- `kAF = μ/id` is multiplicative. -/
lemma kAF_isMult : kAF.IsMultiplicative := ⟨by simp, fun {_ _} hab ↦ by
  simp only [kAF_apply, isMultiplicative_moebius.map_mul_of_coprime hab]
  push_cast; ring⟩

/-- The coprimality indicator `n ↦ [n coprime to m]` as an arithmetic function. -/
noncomputable def coprimeAF (m : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if n = 0 then 0 else if Nat.Coprime n m then 1 else 0, by simp⟩

/-- At `n ≠ 0`, `coprimeAF m n = if (n, m) = 1 then 1 else 0`. -/
lemma coprimeAF_apply_pos (m n : ℕ) (hn : n ≠ 0) :
    coprimeAF m n = if Nat.Coprime n m then 1 else 0 := by
  simp [coprimeAF, hn]

/-- The coprimality indicator is multiplicative. -/
lemma coprimeAF_isMult (m : ℕ) : (coprimeAF m).IsMultiplicative := by
  refine ⟨by simp [coprimeAF], fun {a b} _ ↦ ?_⟩
  rcases eq_or_ne a 0 with ha | ha
  · simp [ha, coprimeAF]
  rcases eq_or_ne b 0 with hb | hb
  · simp [hb, coprimeAF]
  rw [coprimeAF_apply_pos m _ (Nat.mul_ne_zero ha hb), coprimeAF_apply_pos m _ ha,
    coprimeAF_apply_pos m _ hb, ite_zero_mul_ite_zero, mul_one]
  simp only [Nat.coprime_mul_iff_left]

/-- `FmAF m = [·coprime m] · g`, packaged as an arithmetic function, so its `n`-th value is
`if Coprime n m then gKernel n else 0` for `n ≥ 1` (and `0` at `0`). -/
noncomputable def FmAF (m : ℕ) : ArithmeticFunction ℝ := (coprimeAF m).pmul (hfun * kAF)

/-- At `n ≠ 0`, `FmAF m n = if (n, m) = 1 then gKernel n else 0`. -/
lemma FmAF_apply_pos (m n : ℕ) (hn : n ≠ 0) :
    FmAF m n = if Nat.Coprime n m then gKernel n else 0 := by
  simp only [FmAF, ArithmeticFunction.pmul_apply, coprimeAF_apply_pos m n hn, gKernel_eq_mul]
  by_cases h : Nat.Coprime n m <;> simp [h]

/-- `FmAF m` is multiplicative (product of multiplicative functions). -/
lemma FmAF_isMult (m : ℕ) : (FmAF m).IsMultiplicative :=
  (coprimeAF_isMult m).pmul (hfun_isMultiplicative.mul kAF_isMult)

/-- `gKernel (p ^ e)` equals a finite sum over divisor exponents. -/
lemma gKernel_pp_sum (p e : ℕ) (hp : p.Prime) :
    gKernel (p ^ e) = ∑ i ∈ Finset.range (e + 1), hfun (p ^ i) * kAF (p ^ (e - i)) := by
  rw [gKernel_eq_mul, ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal
      (f := fun a b ↦ hfun a * kAF b), Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by simpa using Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) hp.pos]

/-- `hfun (p^i)` is `1` for `i = 0`, `1/(p-1)` for `i = 1`, and `0` for `i ≥ 2`. -/
lemma hfun_pp (p i : ℕ) (hp : p.Prime) :
    hfun (p ^ i) = if i = 0 then (1 : ℝ) else if i = 1 then 1 / ((p : ℝ) - 1) else 0 := by
  simp only [hfun_apply]
  rcases i with _ | _ | i
  · simp
  · rw [if_neg (by omega), if_pos rfl, pow_one, ArithmeticFunction.moebius_apply_prime hp,
      Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega),
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    norm_num

/-- `kAF (p^j)` is `1` for `j = 0`, `-1/p` for `j = 1`, and `0` for `j ≥ 2`. -/
lemma kAF_pp (p j : ℕ) (hp : p.Prime) :
    kAF (p ^ j) = if j = 0 then (1 : ℝ) else if j = 1 then - 1 / (p : ℝ) else 0 := by
  simp only [kAF_apply]
  rcases j with _ | _ | j
  · simp
  · rw [if_neg (by omega), if_pos rfl, pow_one, ArithmeticFunction.moebius_apply_prime hp]
    push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega),
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    norm_num

/-- `g` is supported on cube-free numbers: `gKernel (p^e) = 0` for `e ≥ 3`. -/
lemma gKernel_pp_zero_of_ge (p e : ℕ) (hp : p.Prime) (he : 3 ≤ e) : gKernel (p ^ e) = 0 := by
  rw [gKernel_pp_sum p e hp]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [hfun_pp p i hp, kAF_pp p (e - i) hp]
  split_ifs <;> first | (exfalso; omega) | ring

/-- `gKernel 1 = 1`. -/
lemma gKernel_p0 (p : ℕ) (hp : p.Prime) : gKernel (p ^ 0) = 1 := by
  rw [gKernel_pp_sum p 0 hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hfun_pp p 0 hp, kAF_pp p 0 hp]
  norm_num

/-- `gKernel p = 1/(p-1) - 1/p`. -/
lemma gKernel_p1 (p : ℕ) (hp : p.Prime) : gKernel (p ^ 1) = 1 / ((p : ℝ) - 1) - 1 / p := by
  rw [gKernel_pp_sum p 1 hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hfun_pp p 0 hp, hfun_pp p 1 hp, kAF_pp p 1 hp, kAF_pp p 0 hp]
  norm_num; ring

/-- `gKernel (p²) = -1/((p-1)·p)`. -/
lemma gKernel_p2 (p : ℕ) (hp : p.Prime) : gKernel (p ^ 2) = -(1 / ((p : ℝ) - 1)) * (1 / p) := by
  rw [gKernel_pp_sum p 2 hp]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [hfun_pp p 0 hp, hfun_pp p 1 hp, hfun_pp p 2 hp, kAF_pp p 2 hp, kAF_pp p 1 hp, kAF_pp p 0 hp]
  norm_num; ring

/-- The Euler factor value: `∑_e g(p^e) = 1` at every prime `p`. -/
lemma gKernel_pp_tsum (p : ℕ) (hp : p.Prime) : (∑' e : ℕ, gKernel (p ^ e)) = 1 := by
  rw [tsum_ppow_eq_sum_range _ p 3 (fun e he ↦ gKernel_pp_zero_of_ge p e hp he)]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [gKernel_p0 p hp, gKernel_p1 p hp, gKernel_p2 p hp]
  have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hp.one_lt.ne')
  have hp0 : (p : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  field_simp; ring

/-- The norm of `gKernel` is multiplicative on coprime arguments. -/
lemma gKernel_norm_coprime_mul {a b : ℕ} (h : Nat.Coprime a b) :
    ‖gKernel (a * b)‖ = ‖gKernel a‖ * ‖gKernel b‖ := by
  rw [gKernel_eq_mul, gKernel_eq_mul, gKernel_eq_mul,
    (hfun_isMultiplicative.mul kAF_isMult).map_mul_of_coprime h, norm_mul]

/-- The local sum `∑_e ‖g(p^e)‖` is over the finite support `{0,1,2}`. -/
lemma gKernel_local_summable (p : ℕ) (hp : p.Prime) : Summable (fun e : ℕ ↦ ‖gKernel (p ^ e)‖) := by
  refine summable_of_ne_finset_zero (s := Finset.range 3) fun e he ↦ ?_
  rw [gKernel_pp_zero_of_ge p e hp (by simpa using he), norm_zero]

/-- Uniform per-prime bound: `∑_e ‖g(p^e)‖ ≤ exp(4/p²)`.  Since only `e ∈ {0,1,2}` contribute,
`∑_e ‖g(p^e)‖ = 1 + ‖g(p)‖ + ‖g(p²)‖ ≤ 1 + 4/p² ≤ exp(4/p²)`. -/
lemma gKernel_local_bound (p : ℕ) (hp : p.Prime) :
    (∑' e : ℕ, ‖gKernel (p ^ e)‖) ≤ Real.exp (4 / (p : ℝ) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [tsum_ppow_eq_sum_range (fun n ↦ ‖gKernel n‖) p 3
      (fun e he ↦ by rw [gKernel_pp_zero_of_ge p e hp he, norm_zero])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [gKernel_p0 p hp, gKernel_p1 p hp, gKernel_p2 p hp,
    show 1 / ((p : ℝ) - 1) - 1 / (p : ℝ) = 1 / ((p : ℝ) * ((p : ℝ) - 1)) by field_simp; ring,
    show - (1 / ((p : ℝ) - 1)) * (1 / (p : ℝ)) = -(1 / ((p : ℝ) * ((p : ℝ) - 1))) by field_simp,
    norm_one, norm_neg, Real.norm_of_nonneg (one_div_nonneg.2 (mul_pos hp0 hp1).le)]
  have hkey : 1 / ((p : ℝ) * ((p : ℝ) - 1)) + 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 4 / (p : ℝ) ^ 2 := by
    rw [← add_div, div_le_div_iff₀ (mul_pos hp0 hp1) (pow_pos hp0 2)]
    nlinarith only [mul_nonneg hp0.le (by linarith only [hp2] : (0 : ℝ) ≤ (p : ℝ) - 2)]
  linarith [Real.add_one_le_exp (4 / (p : ℝ) ^ 2)]

/-- `∑ₙ ‖gKernel n‖` converges, by the Euler-factor bound `∑_e ‖g(p^e)‖ ≤ exp(4/p²)`. -/
lemma gKernel_norm_summable : Summable (fun n ↦ ‖gKernel n‖) :=
  summable_of_sum_le (c := Real.exp (∑' n : ℕ, 4 * (1 / (n : ℝ) ^ 2))) (fun n ↦ norm_nonneg _) <|
    finset_sum_le_exp_tsum_of_local (fun n ↦ ‖gKernel n‖)
      (by simp [show gKernel 1 = 1 by simpa using gKernel_p0 2 Nat.prime_two])
      (by simp [gKernel])
      (fun n ↦ norm_nonneg _)
      (fun {a b} h ↦ gKernel_norm_coprime_mul h)
      (fun {p} hp ↦ by simpa only [norm_norm] using gKernel_local_summable p hp)
      (fun n ↦ 4 * (1 / (n : ℝ) ^ 2)) (fun n ↦ by positivity)
      ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left 4)
      (fun p hp ↦ by rw [mul_one_div]; exact gKernel_local_bound p hp)

/-- **L1b-summability.** The norm of `FmAF m` is summable, by domination `‖FmAF m n‖ ≤ ‖gKernel n‖`
and `gKernel_norm_summable`. -/
lemma FmAF_norm_summable (m : ℕ) : Summable (fun n ↦ ‖FmAF m n‖) := by
  refine Summable.of_nonneg_of_le (fun n ↦ norm_nonneg _) (fun n ↦ ?_) gKernel_norm_summable
  rcases eq_or_ne n 0 with hn | hn
  · simp [hn]
  · rw [FmAF_apply_pos m n hn]
    split_ifs <;> simp

/-- **L1b-Euler-factor.** Every local Euler factor of `FmAF m` equals `1`:
at a prime `p ∤ m` the powers of `p` are all coprime to `m`, and `∑_e g(p^e)=1+g(p)+g(p²)=1`;
at a prime `p ∣ m` only `e=0` (i.e. `p^0=1`) is coprime, giving `FmAF m 1 = 1`. -/
lemma FmAF_euler_factor (m : ℕ) (p : Nat.Primes) : (∑' e : ℕ, FmAF m ((p : ℕ) ^ e)) = 1 := by
  have hp : (p : ℕ).Prime := p.2
  have hval : ∀ e : ℕ, FmAF m ((p : ℕ) ^ e) =
      if Nat.Coprime ((p : ℕ) ^ e) m then gKernel ((p : ℕ) ^ e) else 0 :=
    fun e ↦ FmAF_apply_pos m _ (pow_ne_zero e hp.ne_zero)
  simp only [hval]
  by_cases hcop : Nat.Coprime (p : ℕ) m
  · rw [show (fun e : ℕ ↦ if Nat.Coprime ((p : ℕ) ^ e) m then gKernel ((p : ℕ) ^ e) else 0) =
        (fun e : ℕ ↦ gKernel ((p : ℕ) ^ e)) from
      funext fun e ↦ if_pos (hcop.pow_left e), gKernel_pp_tsum (p : ℕ) hp]
  · rw [tsum_eq_single 0 fun e he ↦ if_neg fun hc ↦
      hcop ((Nat.coprime_pow_left_iff (Nat.pos_of_ne_zero he) _ _).1 hc)]
    simpa using gKernel_p0 (p : ℕ) hp

/-- `∑_{(d, m) = 1} gKernel d = 1`, by the Euler product of `FmAF m` and `FmAF_euler_factor`. -/
lemma gKernel_coprime_sum_one (m : ℕ) :
    HasSum (fun d : ℕ ↦ if Nat.Coprime d m then gKernel d else 0) 1 := by
  have hsum := FmAF_norm_summable m
  have hEP := (FmAF_isMult m).eulerProduct_hasProd hsum
  rw [show (fun p : Nat.Primes ↦ ∑' e : ℕ, FmAF m ((p : ℕ) ^ e)) =
        (fun _ : Nat.Primes ↦ (1 : ℝ)) from funext (FmAF_euler_factor m)] at hEP
  have hcongr : (fun d : ℕ ↦ if Nat.Coprime d m then gKernel d else 0) = (FmAF m) := by
    funext n
    rcases eq_or_ne n 0 with hn | hn
    · simp [hn, gKernel]
    · rw [FmAF_apply_pos m n hn]
  rw [hcongr, ← hEP.unique hasProd_one]
  exact (Summable.of_norm hsum).hasSum

/-- **Hyperbola form of `sumA`.**  For `x > 0` the coprime squarefree sum `A(m, x)` is the sum
of `g(a)/b` over the pairs `(a, b)` of positive integers coprime to `m` with `a·b ≤ x`, obtained
by expanding `μ²/φ = g * 1` over the divisor antidiagonal. -/
private lemma sumA_eq_sum_coprimeHyperbola (m : ℕ) (x : ℝ) (hx : 0 < x) :
    PrimeGaps.MaynardOffDiagonal.sumA m x = ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter
          (fun p : ℕ × ℕ ↦ (p.1 * p.2 : ℝ) ≤ x ∧ Nat.Coprime p.1 m ∧ Nat.Coprime p.2 m),
        gKernel p.1 / (p.2 : ℝ) := by
  have hexpand : ∀ f ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun f : ℕ ↦ Nat.Coprime f m),
      ((μ f : ℝ) ^ 2) / (Nat.totient f : ℝ) =
        ∑ ab ∈ f.divisorsAntidiagonal, gKernel ab.1 / (ab.2 : ℝ) := fun f _ ↦ by
    simpa only [mul_one_div] using gKernel_conv_id f
  rw [sumA_eq_mobiusTotientSum, Finset.sum_congr rfl hexpand, ← Finset.sum_biUnion]
  · congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc,
      Nat.mem_divisorsAntidiagonal, Finset.mem_product]
    constructor
    · rintro ⟨f, ⟨⟨hf1, hfle⟩, hfcop⟩, hprod, hfne⟩
      obtain ⟨hcop1, hcop2⟩ := Nat.coprime_mul_iff_left.1 (hprod ▸ hfcop)
      have hp1pos : 1 ≤ p.1 := Nat.pos_of_ne_zero fun h ↦ hfne (by rw [← hprod, h, zero_mul])
      have hp2pos : 1 ≤ p.2 := Nat.pos_of_ne_zero fun h ↦ hfne (by rw [← hprod, h, mul_zero])
      refine ⟨⟨⟨hp1pos, ?_⟩, ⟨hp2pos, ?_⟩⟩, ?_, hcop1, hcop2⟩
      · exact (Nat.le_of_dvd hf1 ⟨p.2, hprod.symm⟩).trans hfle
      · exact (Nat.le_of_dvd hf1 (Dvd.intro_left p.1 hprod)).trans hfle
      · rw [← Nat.cast_mul, hprod]
        exact (Nat.cast_le.2 hfle).trans (Nat.floor_le hx.le)
    · rintro ⟨⟨⟨hp1, hp1le⟩, ⟨hp2, hp2le⟩⟩, hprodle, hcop1, hcop2⟩
      exact ⟨p.1 * p.2, ⟨⟨Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by omega) (by omega)),
        Nat.le_floor (by push_cast; exact hprodle)⟩,
        Nat.coprime_mul_iff_left.2 ⟨hcop1, hcop2⟩⟩, rfl,
        Nat.mul_ne_zero (by omega) (by omega)⟩
  · intro f1 _ f2 _ hne
    simp only [Finset.disjoint_left, Nat.mem_divisorsAntidiagonal]
    rintro p ⟨hprod1, _⟩ ⟨hprod2, _⟩
    exact hne (by rw [← hprod1, ← hprod2])

/-- **Hyperbola form of the convolution sum.**  For `x > 0`, grouping the pairs `(d, k)` of the
hyperbola by their first coordinate turns the sum over the same pairs into
`∑_{d ≤ x, (d,m)=1} g(d) · ∑_{k ≤ x/d, (k,m)=1} 1/k`. -/
private lemma sum_gKernel_mul_crs_eq_sum_coprimeHyperbola (m : ℕ) (x : ℝ) (hx : 0 < x) :
    (∑ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m),
        gKernel d * coprimeReciprocalSum m (x / d)) =
      ∑ p ∈ (Finset.Icc 1 ⌊x⌋₊ ×ˢ Finset.Icc 1 ⌊x⌋₊).filter
          (fun p : ℕ × ℕ ↦ (p.1 * p.2 : ℝ) ≤ x ∧ Nat.Coprime p.1 m ∧ Nat.Coprime p.2 m),
        gKernel p.1 / (p.2 : ℝ) := by
  set K : ℕ → Finset ℕ := fun d ↦
    (Finset.Icc 1 ⌊x / d⌋₊).filter (fun k : ℕ ↦ Nat.Coprime k m) with hKdef
  have hstep : ∀ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m),
      gKernel d * coprimeReciprocalSum m (x / d) =
        ∑ p ∈ (K d).map ⟨fun k ↦ (d, k), fun a b h ↦ by simpa using h⟩,
          gKernel p.1 / (p.2 : ℝ) := fun d _ ↦ by
    rw [Finset.sum_map, coprimeReciprocalSum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ ↦ mul_one_div _ _
  rw [Finset.sum_congr rfl hstep, ← Finset.sum_biUnion]
  · congr 1
    ext p
    simp only [Finset.mem_biUnion, Finset.mem_map,
      hKdef, Finset.mem_filter, Finset.mem_Icc, Finset.mem_product]
    constructor
    · rintro ⟨d, ⟨⟨hd1, hdle⟩, hdcop⟩, k, ⟨⟨hk1, hkle⟩, hkcop⟩, rfl⟩
      have hd0r : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
      have hprodle : (d : ℝ) * k ≤ x := by
        rw [mul_comm]
        exact (le_div_iff₀ hd0r).1 ((Nat.le_floor_iff (by positivity)).1 hkle)
      refine ⟨⟨⟨hd1, hdle⟩, ⟨hk1, Nat.le_floor ?_⟩⟩, hprodle, hdcop, hkcop⟩
      exact le_trans (le_mul_of_one_le_left (by positivity) (by exact_mod_cast hd1)) hprodle
    · rintro ⟨⟨⟨hp1, hp1le⟩, ⟨hp2, hp2le⟩⟩, hprodle, hcop1, hcop2⟩
      refine ⟨p.1, ⟨⟨hp1, hp1le⟩, hcop1⟩, p.2, ⟨⟨hp2, ?_⟩, hcop2⟩, rfl⟩
      rw [Nat.le_floor_iff (by positivity), le_div_iff₀ (by exact_mod_cast hp1 : (0 : ℝ) < p.1)]
      linarith
  · intro d1 _ d2 _ hne
    simp only [Finset.disjoint_left, Finset.mem_map]
    rintro p ⟨_, _, hp1⟩ ⟨_, _, hp2⟩
    exact hne (congrArg Prod.fst (hp1.trans hp2.symm))

/-- Hyperbola form of `sumA`: `A(m, x) = ∑_{d ≤ x, (d, m) = 1} g(d) · ∑_{k ≤ x/d, (k, m) = 1} 1/k`,
obtained from `μ²/φ = g ∗ (1/id)` by interchanging the two summations. -/
lemma sumA_eq_conv (m : ℕ) (x : ℝ) : PrimeGaps.MaynardOffDiagonal.sumA m x =
      ∑ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m),
        gKernel d * coprimeReciprocalSum m (x / d) := by
  by_cases hx1 : x < 1
  · rw [PrimeGaps.MaynardOffDiagonal.sumA, PrimeGaps.MaynardOffDiagonal.Sset,
      Nat.floor_eq_zero.mpr hx1]
    simp
  push Not at hx1
  have hxpos : (0 : ℝ) < x := zero_lt_one.trans_le hx1
  rw [sumA_eq_sum_coprimeHyperbola m x hxpos, sum_gKernel_mul_crs_eq_sum_coprimeHyperbola m x hxpos]

end PrimeGaps
