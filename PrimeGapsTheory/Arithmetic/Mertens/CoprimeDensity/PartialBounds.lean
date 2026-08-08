/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeDensity.GKernel

import PrimeGapsTheory.ArithmeticFunction.Estimates

/-!
# Partial bounds for the kernel

Multiplicative majorants for `gKernel` and the resulting partial-sum bounds.

## Main results

* `gKernel_partial_weighted_bound`
-/

@[expose] public section

open Real

open PrimeGaps.MertensShared Finset ArithmeticFunction

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

/-- `b(n) = μ(n)²/(φ(n)·n)`, a nonnegative multiplicative function supported on squarefree `n`. -/
noncomputable def bAF : ArithmeticFunction ℝ :=
  ⟨fun n ↦ (μ n : ℝ) ^ 2 / ((Nat.totient n : ℝ) * (n : ℝ)), by simp⟩

/-- `bAF n = μ(n)²/(φ(n)·n)`. -/
@[simp] lemma bAF_apply (n : ℕ) :
    bAF n = (μ n : ℝ) ^ 2 / ((Nat.totient n : ℝ) * (n : ℝ)) := rfl

/-- `bAF` is nonnegative. -/
lemma bAF_nonneg (n : ℕ) : 0 ≤ bAF n := by
  rw [bAF_apply]; positivity

/-- `bAF = μ²/(φ·id)` is multiplicative. -/
lemma bAF_isMult : bAF.IsMultiplicative := by
  refine ⟨by simp, fun {a b} hab ↦ ?_⟩
  simp only [bAF_apply, isMultiplicative_moebius.2 hab, Nat.totient_mul hab]
  push_cast; ring

/-- `bAF (p^k)` is `1` for `k = 0`, `1/(p·(p-1))` for `k = 1`, and `0` for `k ≥ 2`. -/
lemma bAF_pp (p k : ℕ) (hp : p.Prime) : bAF (p ^ k) =
    if k = 0 then (1 : ℝ) else if k = 1 then 1 / ((p : ℝ) * ((p : ℝ) - 1)) else 0 := by
  simp only [bAF_apply]
  rcases k with _ | _ | k
  · simp
  · rw [if_neg (by omega), if_pos rfl, pow_one, ArithmeticFunction.moebius_apply_prime hp,
      Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    push_cast; ring
  · rw [if_neg (by omega), if_neg (by omega),
      ArithmeticFunction.moebius_apply_prime_pow hp (by omega)]
    norm_num

/-- Per-prime bound `∑_k bAF (p^k) = 1 + 1/(p·(p-1)) ≤ exp(2/p²)`. -/
lemma bAF_local_bound (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, bAF (p ^ k)) ≤ rexp (2 / (p : ℝ) ^ 2) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [tsum_ppow_eq_sum_range _ p 2
      (fun e he ↦ by rw [bAF_pp p e hp, if_neg (by omega), if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [bAF_pp p 0 hp, bAF_pp p 1 hp, if_pos rfl, if_neg one_ne_zero, if_pos rfl]
  have hkey : 1 / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 / (p : ℝ) ^ 2 := by
    rw [div_le_div_iff₀ (mul_pos hp0 hp1) (pow_pos hp0 2)]
    nlinarith
  linarith [Real.add_one_le_exp (2 / (p : ℝ) ^ 2)]

/-- Absolute uniform bound on the partial sums of `b`. -/
lemma sum_bAF_le :
    ∀ N : ℕ, (∑ d ∈ Finset.Icc 1 N, bAF d) ≤ rexp (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2) := by
  intro N
  have key := finset_sum_le_exp_tsum_of_local (fun n ↦ bAF n) bAF_isMult.1 bAF.map_zero
    bAF_nonneg (fun {a b} h ↦ bAF_isMult.2 h)
    (fun {p} hp ↦ summable_of_ne_finset_zero (s := Finset.range 2) fun e he ↦ by
      rw [Finset.mem_range, not_lt] at he
      rw [bAF_pp p e hp, if_neg (by omega), if_neg (by omega), norm_zero])
    (fun n ↦ 2 * (1 / (n : ℝ) ^ 2)) (fun n ↦ by positivity)
    (((Real.summable_one_div_nat_pow).mpr (by norm_num)).mul_left 2)
    (fun p hp ↦ by rw [mul_one_div]; exact bAF_local_bound p hp)
    (Finset.Icc 1 N)
  rwa [tsum_mul_left] at key

/-- `∑_{r ≤ N} 1/φ(r) ≤ A · (1 + log N)` for an absolute constant `A > 0`. -/
lemma sum_recip_totient_le : ∃ A : ℝ, 0 < A ∧ ∀ N : ℕ,
      (∑ r ∈ Finset.Icc 1 N, (1 : ℝ) / (r.totient : ℝ)) ≤ A * (1 + Real.log N) := by
  classical
  set Cb : ℝ := rexp (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ 2)
  have hCbpos : 0 < Cb := Real.exp_pos _
  refine ⟨Cb, hCbpos, ?_⟩
  intro N
  rcases Nat.eq_zero_or_pos N with hN0 | hNpos
  · subst hN0
    simp only [Order.lt_one_iff, Icc_eq_empty_of_lt, one_div, sum_empty, CharP.cast_eq_zero,
      Real.log_zero, add_zero, mul_one]
    positivity
  have hlogN : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hNpos)
  have hterm : ∀ r ∈ Finset.Icc 1 N, (1 : ℝ) / (r.totient : ℝ) =
      ∑ dk ∈ r.divisorsAntidiagonal, bAF dk.1 / (dk.2 : ℝ) := by
    intro r hr
    rw [Finset.mem_Icc] at hr
    have hr0 : r ≠ 0 := by omega
    have hid : (1 : ℝ) / (r.totient : ℝ) = (1 / (r : ℝ)) * ∑ d ∈ r.divisors,
            (μ d : ℝ) ^ 2 / (Nat.totient d : ℝ) := by
      rw [ArithmeticFunction.sum_moebius_sq_div_totient]; field_simp
    rw [hid, Finset.mul_sum, Nat.sum_divisorsAntidiagonal (f := fun d k ↦ bAF d / (k : ℝ))]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    obtain ⟨⟨k, hk⟩, -⟩ := Nat.mem_divisors.mp hd
    have hd0 : d ≠ 0 := by rintro h; rw [h, zero_mul] at hk; exact hr0 hk
    have hk0 : k ≠ 0 := by rintro h; rw [h, mul_zero] at hk; exact hr0 hk
    rw [show r / d = k from by rw [hk]; exact Nat.mul_div_cancel_left k (Nat.pos_of_ne_zero hd0),
      bAF_apply, show (r : ℝ) = (d : ℝ) * (k : ℝ) from by rw [hk]; push_cast; ring]
    field_simp
  set T : Finset (ℕ × ℕ) := (Finset.Icc 1 N ×ˢ Finset.Icc 1 N).filter
      (fun p : ℕ × ℕ ↦ p.1 * p.2 ≤ N) with hT_def
  have hflat : (∑ r ∈ Finset.Icc 1 N, ∑ dk ∈ r.divisorsAntidiagonal, bAF dk.1 / (dk.2 : ℝ)) =
      ∑ p ∈ T, bAF p.1 / (p.2 : ℝ) := by
    rw [← Finset.sum_biUnion]
    · congr 1
      ext p
      simp only [Finset.mem_biUnion, hT_def, Finset.mem_filter, Finset.mem_Icc,
        Nat.mem_divisorsAntidiagonal, Finset.mem_product]
      constructor
      · rintro ⟨r, ⟨hr1, hrN⟩, rfl, hrne⟩
        obtain ⟨h1, h2⟩ := Nat.mul_ne_zero_iff.mp hrne
        exact ⟨⟨⟨Nat.pos_of_ne_zero h1,
            (Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h2)).trans hrN⟩,
          Nat.pos_of_ne_zero h2, (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h1)).trans hrN⟩, hrN⟩
      · rintro ⟨⟨⟨hp1, hp1le⟩, hp2, hp2le⟩, hprodle⟩
        exact ⟨p.1 * p.2, ⟨Nat.one_le_iff_ne_zero.mpr
          (Nat.mul_ne_zero (by omega) (by omega)), hprodle⟩, rfl,
          Nat.mul_ne_zero (by omega) (by omega)⟩
    · intro r1 hr1 r2 hr2 hne
      simp only [Finset.disjoint_left, Nat.mem_divisorsAntidiagonal]
      rintro p ⟨hprod1, _⟩ ⟨hprod2, _⟩
      exact hne (by rw [← hprod1, ← hprod2])
  set K : ℕ → Finset ℕ := fun d ↦ {k ∈ (Finset.Icc 1 N) | d * k ≤ N} with hK_def
  have hgroup : (∑ p ∈ T, bAF p.1 / (p.2 : ℝ)) =
      ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ K d, bAF d / (k : ℝ) := by
    rw [hT_def, Finset.sum_filter, Finset.sum_product]
    exact Finset.sum_congr rfl fun d _ ↦ by rw [hK_def, Finset.sum_filter]
  have hinner : ∀ d ∈ Finset.Icc 1 N, ∑ k ∈ K d, bAF d / (k : ℝ) ≤ bAF d * (1 + Real.log N) := by
    intro d _
    have hharm : ∑ k ∈ K d, (1 : ℝ) / (k : ℝ) ≤ 1 + Real.log N := by
      have hKsub : K d ⊆ Finset.Icc 1 N := by rw [hK_def]; exact Finset.filter_subset _ _
      refine (Finset.sum_le_sum_of_subset_of_nonneg hKsub
        fun k _ _ ↦ by positivity).trans ?_
      rw [← harmonic_cast_eq_sum]; exact harmonic_le_one_add_log N
    calc ∑ k ∈ K d, bAF d / (k : ℝ) = bAF d * ∑ k ∈ K d, (1 : ℝ) / (k : ℝ) := by
          simp only [Finset.mul_sum, mul_one_div]
      _ ≤ bAF d * (1 + Real.log N) := mul_le_mul_of_nonneg_left hharm (bAF_nonneg d)
  rw [Finset.sum_congr rfl hterm, hflat, hgroup]
  calc ∑ d ∈ Finset.Icc 1 N, ∑ k ∈ K d, bAF d / (k : ℝ)
      ≤ ∑ d ∈ Finset.Icc 1 N, bAF d * (1 + Real.log N) := Finset.sum_le_sum hinner
    _ = (∑ d ∈ Finset.Icc 1 N, bAF d) * (1 + Real.log N) := by rw [Finset.sum_mul]
    _ ≤ Cb * (1 + Real.log N) := mul_le_mul_of_nonneg_right (sum_bAF_le N) (by linarith)

/-- `wsqAF n = |g(n)|*sqrt n`, an arithmetic function; multiplicative and nonneg. -/
noncomputable def wsqAF : ArithmeticFunction ℝ :=
  ⟨fun n ↦ |gKernel n| * √n, by simp⟩

/-- `wsqAF n = |gKernel n| · √n`. -/
@[simp] lemma wsqAF_apply (n : ℕ) : wsqAF n = |gKernel n| * √n := rfl

/-- `wsqAF` is nonnegative. -/
lemma wsqAF_nonneg (n : ℕ) : 0 ≤ wsqAF n := by
  rw [wsqAF_apply]; positivity

/-- `wsqAF = |g|·√· ` is multiplicative. -/
lemma wsqAF_isMult : wsqAF.IsMultiplicative := by
  refine ⟨by simp [gKernel], fun {a b} hab ↦ ?_⟩
  have hnorm := gKernel_norm_coprime_mul hab
  simp only [Real.norm_eq_abs] at hnorm
  simp only [wsqAF_apply, hnorm, Nat.cast_mul, Real.sqrt_mul (Nat.cast_nonneg a)]
  ring

/-- Weight attached to the square part: `hfacB b := |gKernel (b^2)| * b`. -/
noncomputable def hfacB (b : ℕ) : ℝ := |gKernel (b ^ 2)| * (b : ℝ)

/-- `hfacB` is nonnegative. -/
lemma hfacB_nonneg (b : ℕ) : 0 ≤ hfacB b := by
  rw [hfacB]; positivity

/-- `n ↦ |gKernel (n²)|` packaged as an arithmetic function. -/
noncomputable def sqAbsG : ArithmeticFunction ℝ :=
  ⟨fun n ↦ |gKernel (n ^ 2)|, by simp [gKernel]⟩

/-- `sqAbsG n = |gKernel (n²)|`. -/
@[simp] lemma sqAbsG_apply (n : ℕ) : sqAbsG n = |gKernel (n ^ 2)| := rfl

/-- `sqAbsG` is multiplicative, since `(a, b) = 1` implies `(a², b²) = 1`. -/
lemma sqAbsG_isMult : sqAbsG.IsMultiplicative := by
  refine ⟨by simp [gKernel], fun {a b} hab ↦ ?_⟩
  have hnorm := gKernel_norm_coprime_mul (Nat.Coprime.pow 2 2 hab)
  simp only [Real.norm_eq_abs] at hnorm
  simp only [sqAbsG_apply, mul_pow, hnorm]

/-- `|gKernel (p^2)| = 1/((p-1)*p)` for a prime `p`. -/
lemma abs_gKernel_p2 (p : ℕ) (hp : p.Prime) : |gKernel (p ^ 2)| = 1 / (((p : ℝ) - 1) * p) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  rw [gKernel_p2 p hp, abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg
    (by simp only [neg_nonpos]; positivity) (by positivity))]
  field_simp

/-- For squarefree `b >= 1`, `hfacB b = 1/phi(b)`. -/
lemma hfacB_eq_recip_totient (b : ℕ) (hb : b ≠ 0) (hsq : Squarefree b) :
    hfacB b = 1 / (b.totient : ℝ) := by
  have hfac : |gKernel (b ^ 2)| = ∏ p ∈ b.primeFactors, |gKernel (p ^ 2)| := by
    simpa only [sqAbsG_apply] using (sqAbsG_isMult.prod_primeFactors (l := b) hsq).symm
  have hbprod : (b : ℝ) = ∏ p ∈ b.primeFactors, (p : ℝ) := by
    rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
  have hphi : (b.totient : ℝ) = ∏ p ∈ b.primeFactors, ((p : ℝ) - 1) :=
    PrimeGaps.totient_eq_prod_sub_one b (Nat.pos_of_ne_zero hb) hsq
  have key : ∀ p ∈ b.primeFactors, |gKernel (p ^ 2)| * (p : ℝ) = 1 / ((p : ℝ) - 1) := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    have h1 : (1 : ℝ) < p := by exact_mod_cast hp'.one_lt
    have h0 : (0 : ℝ) < (p : ℝ) := by linarith
    rw [abs_gKernel_p2 p hp']; field_simp
  rw [hfacB, hfac, hbprod, hphi, ← Finset.prod_mul_distrib, Finset.prod_congr rfl key,
    Finset.prod_div_distrib, Finset.prod_const_one]

/-- `vAF n = if Squarefree n then wsqAF n else 0`, a nonneg multiplicative arithmetic
function agreeing with `wsqAF` on squarefree numbers and vanishing elsewhere. -/
noncomputable def vAF : ArithmeticFunction ℝ :=
  ⟨fun n ↦ if Squarefree n then |gKernel n| * √n else 0, by simp⟩

/-- `vAF n = if Squarefree n then |gKernel n| · √n else 0`. -/
lemma vAF_apply (n : ℕ) : vAF n = if Squarefree n then |gKernel n| * √n else 0 := rfl

/-- `vAF` is nonnegative. -/
lemma vAF_nonneg (n : ℕ) : 0 ≤ vAF n := by
  rw [vAF_apply]; split <;> positivity

/-- `vAF` is multiplicative, squarefreeness being multiplicative on coprime arguments. -/
lemma vAF_isMult : vAF.IsMultiplicative := by
  refine ⟨by simp [vAF_apply, gKernel], fun {a b} hab ↦ ?_⟩
  simp only [vAF_apply]
  by_cases hsa : Squarefree a
  · by_cases hsb : Squarefree b
    · rw [if_pos ((Nat.squarefree_mul hab).mpr ⟨hsa, hsb⟩), if_pos hsa, if_pos hsb]
      simpa using wsqAF_isMult.map_mul_of_coprime hab
    · rw [if_neg fun h ↦ hsb ((Nat.squarefree_mul hab).mp h).2, if_neg hsb, mul_zero]
  · rw [if_neg fun h ↦ hsa ((Nat.squarefree_mul hab).mp h).1, if_neg hsa, zero_mul]

/-- `vAF (p^k)` is `1` for `k=0`, `√p/(p·(p-1))` for `k=1`, and `0` for `k≥2`. -/
lemma vAF_pp (p k : ℕ) (hp : p.Prime) : vAF (p ^ k) = if k = 0 then (1 : ℝ)
      else if k = 1 then √p / ((p : ℝ) * ((p : ℝ) - 1)) else 0 := by
  rw [vAF_apply]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rcases k with _ | _ | k
  · simp [gKernel]
  · rw [pow_one, if_pos (by simpa using hp.squarefree), if_neg (by omega), if_pos rfl,
      show gKernel p = 1 / ((p : ℝ) - 1) - 1 / p from by simpa using gKernel_p1 p hp,
      abs_of_nonneg (by
        rw [sub_nonneg]
        exact div_le_div_of_nonneg_left (by norm_num) hpm1 (by linarith))]
    have hsqrt_sq : √p * √p = (p : ℝ) := Real.mul_self_sqrt hp0.le
    have hsqrtpos : (0 : ℝ) < √p := Real.sqrt_pos.mpr hp0
    field_simp
    nlinarith [hsqrt_sq, hsqrtpos, hpm1, hp0]
  · rw [if_neg (by
      rw [Nat.squarefree_pow_iff hp.ne_one (by omega)]
      rintro ⟨-, h⟩
      omega), if_neg (by omega), if_neg (by omega)]

/-- Per-prime bound `∑_k vAF (p^k) = 1 + √p/(p(p-1)) ≤ exp(2/p^(3/2))`. -/
lemma vAF_local_bound (p : ℕ) (hp : p.Prime) :
    (∑' k : ℕ, vAF (p ^ k)) ≤ rexp (2 / (p : ℝ) ^ ((3 : ℝ) / 2)) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpm1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [tsum_ppow_eq_sum_range _ p 2
      (fun e he ↦ by rw [vAF_pp p e hp, if_neg (by omega), if_neg (by omega)])]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [vAF_pp p 0 hp, vAF_pp p 1 hp, if_pos rfl, if_neg one_ne_zero, if_pos rfl]
  have hsqrt_sq : √p * √p = (p : ℝ) := Real.mul_self_sqrt hp0.le
  have hsqrtpos : (0 : ℝ) < √p := Real.sqrt_pos.mpr hp0
  have hkey : √p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 2 / (p : ℝ) ^ ((3 : ℝ) / 2) := by
    rw [show (p : ℝ) ^ ((3 : ℝ) / 2) = (p : ℝ) * √p from by
        rw [Real.sqrt_eq_rpow, show (3 : ℝ) / 2 = 1 + 1 / 2 from by ring, Real.rpow_add hp0,
          Real.rpow_one],
      div_le_div_iff₀ (mul_pos hp0 hpm1) (mul_pos hp0 hsqrtpos)]
    nlinarith [hsqrt_sq]
  linarith [Real.add_one_le_exp (2 / (p : ℝ) ^ ((3 : ℝ) / 2))]

/-- `∑_{a ≤ X, a squarefree} |gKernel a| · √a ≤ C₀` uniformly in `X`, since `∑_p p^(-3/2)`
converges. -/
lemma wsqAF_sqfree_sum_bound : ∃ C0 : ℝ, 0 < C0 ∧ ∀ X : ℕ,
      (∑ a ∈ {a ∈ (Finset.Icc 1 X) | Squarefree a}, wsqAF a) ≤ C0 := by
  refine ⟨rexp (2 * ∑' n : ℕ, 1 / (n : ℝ) ^ ((3 : ℝ) / 2)), Real.exp_pos _, ?_⟩
  intro X
  have hrw : (∑ a ∈ {a ∈ (Finset.Icc 1 X) | Squarefree a}, wsqAF a) =
      ∑ a ∈ Finset.Icc 1 X, vAF a := by
    rw [Finset.sum_filter]
    exact Finset.sum_congr rfl fun a _ ↦ by rw [vAF_apply, wsqAF_apply]
  rw [hrw]
  have key := finset_sum_le_exp_tsum_of_local (fun n ↦ vAF n) vAF_isMult.1 vAF.map_zero
    vAF_nonneg (fun {a b} h ↦ vAF_isMult.2 h)
    (fun {p} hp ↦ summable_of_ne_finset_zero (s := Finset.range 2) fun e he ↦ by
      rw [Finset.mem_range, not_lt] at he
      rw [vAF_pp p e hp, if_neg (by omega), if_neg (by omega), norm_zero])
    (fun n ↦ 2 * (1 / (n : ℝ) ^ ((3 : ℝ) / 2))) (fun n ↦ by positivity)
    (((Real.summable_one_div_nat_rpow).mpr (by norm_num)).mul_left 2)
    (fun p hp ↦ by rw [mul_one_div]; exact vAF_local_bound p hp)
    (Finset.Icc 1 X)
  rwa [tsum_mul_left] at key

/-- `gKernel` is supported on cube-free numbers: `gKernel d ≠ 0` forces every exponent in the
factorisation of `d` to be at most `2`. -/
lemma cubefree_support {d : ℕ} (hd : gKernel d ≠ 0) : ∀ p, d.factorization p ≤ 2 := by
  intro p
  by_contra hlt
  push Not at hlt
  have hdne : d ≠ 0 := by rintro rfl; exact hd (by simp [gKernel])
  have hpp : p.Prime := by
    by_contra hp
    rw [Nat.factorization_eq_zero_of_not_prime d hp] at hlt
    omega
  set e := d.factorization p with he
  set m := d / p ^ e
  have hdecomp : p ^ e * m = d := Nat.ordProj_mul_ordCompl_eq_self d p
  have hcop : Nat.Coprime (p ^ e) m := (Nat.coprime_ordCompl hpp hdne).pow_left e
  have hnorm : ‖gKernel d‖ = ‖gKernel (p ^ e)‖ * ‖gKernel m‖ := by
    rw [← hdecomp]; exact gKernel_norm_coprime_mul hcop
  rw [gKernel_pp_zero_of_ge p e hpp (by omega), norm_zero, zero_mul] at hnorm
  exact hd (by simpa [Real.norm_eq_abs, abs_eq_zero] using hnorm)

/-- For the square-decomposition `d = b²·a` with `(a, b) = 1`, `wsqAF d = wsqAF a · hfacB b`. -/
lemma wsqAF_pair_eq {a b d : ℕ} (hd : d = b ^ 2 * a) (hab : Nat.Coprime a b) :
    wsqAF d = wsqAF a * hfacB b := by
  rw [show d = a * b ^ 2 from by rw [hd]; ring,
    wsqAF_isMult.map_mul_of_coprime (hab.pow_right 2), wsqAF_apply (b ^ 2), hfacB]
  congr 1
  rw [Nat.cast_pow, Real.sqrt_sq (by positivity)]

/-- `hfacB b ≤ 1/φ(b)`, with equality for squarefree `b` and `hfacB b = 0` otherwise. -/
lemma hfacB_le_recip_totient {b : ℕ} (hb : 1 ≤ b) : hfacB b ≤ (1 : ℝ) / (b.totient : ℝ) := by
  have hb0 : b ≠ 0 := by omega
  by_cases hsq : Squarefree b
  · rw [hfacB_eq_recip_totient b hb0 hsq]
  · have hgz : gKernel (b ^ 2) = 0 := by
      by_contra hne
      rw [Nat.squarefree_iff_factorization_le_one hb0] at hsq
      push Not at hsq
      obtain ⟨p, hp⟩ := hsq
      have hcf := cubefree_support hne p
      have hfact : (b ^ 2).factorization p = 2 * b.factorization p := by
        rw [Nat.factorization_pow]; simp
      omega
    rw [hfacB, hgz, abs_zero, zero_mul]
    positivity

/-- **Square-part decomposition of a cube-free `d`.**  If `1 ≤ d ≤ X` has `g(d) ≠ 0`, so that
every exponent in `d` is at most `2`, and `d = b²·a`, then `a` and `b` are coprime, `1 ≤ a ≤ X`
and `1 ≤ b` with `b² ≤ X`. -/
private lemma sq_mul_squarefree_props {X d a b : ℕ} (hd1 : 1 ≤ d) (hdX : d ≤ X)
    (hgne : gKernel d ≠ 0) (heq : b ^ 2 * a = d) :
    (1 ≤ a ∧ a ≤ X) ∧ (1 ≤ b ∧ b ^ 2 ≤ X) ∧ Nat.Coprime a b := by
  have hane : a ≠ 0 := by rintro h0; rw [h0, mul_zero] at heq; omega
  have hbne : b ≠ 0 := by rintro h0; rw [h0] at heq; simp at heq; omega
  have ha1 : 1 ≤ a := Nat.one_le_iff_ne_zero.mpr hane
  have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hbne
  have hcop : Nat.Coprime a b := by
    rw [Nat.coprime_iff_gcd_eq_one]
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := (Nat.gcd a b).exists_prime_and_dvd hne
    have hfa1 : 1 ≤ a.factorization p := (hp.pow_dvd_iff_le_factorization hane).mp
      (by simpa using hpdvd.trans (Nat.gcd_dvd_left a b))
    have hfb1 : 1 ≤ b.factorization p := (hp.pow_dvd_iff_le_factorization hbne).mp
      (by simpa using hpdvd.trans (Nat.gcd_dvd_right a b))
    have hfact : d.factorization p = 2 * b.factorization p + a.factorization p := by
      subst heq
      simp [Nat.factorization_mul (pow_ne_zero 2 hbne) hane, Nat.factorization_pow]
    have := cubefree_support hgne p
    omega
  have hdX' : b ^ 2 * a ≤ X := by rw [heq]; exact hdX
  exact ⟨⟨ha1, (Nat.le_mul_of_pos_left a (by positivity)).trans hdX'⟩,
    ⟨hb1, (Nat.le_mul_of_pos_right _ ha1).trans hdX'⟩, hcop⟩

/-- **The cube-free reindexing inequality.** -/
lemma cubefree_pair_bound (X : ℕ) (C0 : ℝ) (hC0 : 0 < C0)
    (hInner : ∀ Y : ℕ, (∑ a ∈ {a ∈ (Finset.Icc 1 Y) | Squarefree a}, wsqAF a) ≤ C0) :
    (∑ d ∈ Finset.Icc 1 X, |gKernel d| * (d : ℝ) / √d) ≤
      C0 * ∑ b ∈ Finset.Icc 1 (Nat.sqrt X), (1 : ℝ) / (b.totient : ℝ) := by
  classical
  set S := Finset.Icc 1 X with hS
  set A := {a ∈ (Finset.Icc 1 X) | Squarefree a} with hA
  set B := Finset.Icc 1 (Nat.sqrt X) with hB
  have hstage0 : (∑ d ∈ S, |gKernel d| * (d : ℝ) / √d) = ∑ d ∈ S, wsqAF d :=
    Finset.sum_congr rfl fun d _ ↦ by rw [wsqAF_apply, mul_div_assoc, Real.div_sqrt]
  set T := {d ∈ S | gKernel d ≠ 0} with hT
  have hstage1 : (∑ d ∈ S, wsqAF d) = ∑ d ∈ T, wsqAF d := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) fun d hdS hdT ↦ ?_).symm
    rw [wsqAF_apply, not_not.mp (fun hg ↦ hdT (Finset.mem_filter.mpr ⟨hdS, hg⟩)),
      abs_zero, zero_mul]
  set fa : ℕ → ℕ := fun d ↦ (Nat.sq_mul_squarefree d).choose
  set fb : ℕ → ℕ := fun d ↦ (Nat.sq_mul_squarefree d).choose_spec.choose
  have hspec : ∀ d, fb d ^ 2 * fa d = d ∧ Squarefree (fa d) :=
    fun d ↦ (Nat.sq_mul_squarefree d).choose_spec.choose_spec
  have hprops : ∀ d ∈ T, fa d ∈ A ∧ fb d ∈ B ∧ Nat.Coprime (fa d) (fb d) := by
    intro d hdT
    rw [hT, Finset.mem_filter, hS, Finset.mem_Icc] at hdT
    obtain ⟨heq, hasf⟩ := hspec d
    obtain ⟨⟨ha1, haX⟩, ⟨hb1, hbX⟩, hcop⟩ := sq_mul_squarefree_props hdT.1.1 hdT.1.2 hdT.2 heq
    exact ⟨by rw [hA, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨ha1, haX⟩, hasf⟩,
      by rw [hB, Finset.mem_Icc]; exact ⟨hb1, Nat.le_sqrt'.mpr hbX⟩, hcop⟩
  have hval : ∀ d ∈ T, wsqAF d = wsqAF (fa d) * hfacB (fb d) :=
    fun d hdT ↦ wsqAF_pair_eq (hspec d).1.symm (hprops d hdT).2.2
  have hinj : Set.InjOn (fun d ↦ (fa d, fb d)) (T : Set ℕ) := by
    intro d1 _ d2 _ heqp
    simp only [Prod.mk.injEq] at heqp
    calc d1 = fb d1 ^ 2 * fa d1 := (hspec d1).1.symm
      _ = fb d2 ^ 2 * fa d2 := by rw [heqp.1, heqp.2]
      _ = d2 := (hspec d2).1
  have himg : (∑ d ∈ T, wsqAF d) =
      ∑ p ∈ T.image (fun d ↦ (fa d, fb d)), (wsqAF p.1 * hfacB p.2) := by
    rw [Finset.sum_image (fun x hx y hy h ↦ hinj hx hy h)]
    exact Finset.sum_congr rfl hval
  have hsub : T.image (fun d ↦ (fa d, fb d)) ⊆ A ×ˢ B := by
    intro p hp
    obtain ⟨d, hdT, rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨(hprops d hdT).1, (hprops d hdT).2.1⟩
  rw [hstage0, hstage1, himg]
  calc (∑ p ∈ T.image (fun d ↦ (fa d, fb d)), (wsqAF p.1 * hfacB p.2))
      ≤ ∑ p ∈ A ×ˢ B, (wsqAF p.1 * hfacB p.2) :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub
          fun p _ _ ↦ mul_nonneg (wsqAF_nonneg _) (hfacB_nonneg _)
    _ = (∑ a ∈ A, wsqAF a) * ∑ b ∈ B, hfacB b := by
        rw [Finset.sum_mul_sum, Finset.sum_product]
    _ ≤ C0 * ∑ b ∈ B, (1 : ℝ) / (b.totient : ℝ) := by
        refine mul_le_mul (hInner X) (Finset.sum_le_sum fun b hb ↦ ?_)
          (Finset.sum_nonneg fun b _ ↦ hfacB_nonneg b) hC0.le
        rw [hB, Finset.mem_Icc] at hb
        exact hfacB_le_recip_totient hb.1

/-- **Inner-sum reduction.**  There is an absolute constant `B > 0` with
`sum_{d <= X} |g(d)|*d/sqrt d <= B * sum_{r <= sqrt X} 1/phi(r)` for every `X`. -/
lemma sqrtnorm_le_const_mul_totient_sum : ∃ B : ℝ, 0 < B ∧ ∀ X : ℕ,
      (∑ d ∈ Finset.Icc 1 X, |gKernel d| * (d : ℝ) / √d) ≤
        B * ∑ r ∈ Finset.Icc 1 (Nat.sqrt X), (1 : ℝ) / (r.totient : ℝ) := by
  obtain ⟨C0, hC0pos, hC0⟩ := wsqAF_sqfree_sum_bound
  exact ⟨C0, hC0pos, fun X ↦ cubefree_pair_bound X C0 hC0pos hC0⟩

/-- **Log arithmetic.** `1 + log(√X) ≤ (1/log 2)·log(2X)` for `X ≥ 1`. -/
lemma log_sqrt_arith_bound (X : ℕ) (hX : 1 ≤ X) :
    1 + Real.log (Nat.sqrt X) ≤ (1 / Real.log 2) * Real.log (2 * X) := by
  have hXr : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogX : (0 : ℝ) ≤ Real.log X := Real.log_nonneg hXr
  have hns_le : (Nat.sqrt X : ℝ) ≤ √X :=
    Real.le_sqrt_of_sq_le (by exact_mod_cast Nat.sqrt_le' X)
  have hlogns : Real.log (Nat.sqrt X) ≤ (1 / 2) * Real.log X := by
    rcases Nat.eq_zero_or_pos (Nat.sqrt X) with h0 | hpos
    · simp only [h0, CharP.cast_eq_zero, Real.log_zero]; linarith
    · have h1 := Real.log_le_log (by exact_mod_cast hpos : (0 : ℝ) < (Nat.sqrt X : ℝ)) hns_le
      rw [Real.log_sqrt hXpos.le] at h1
      linarith
  have hcoef : (1 : ℝ) / 2 ≤ 1 / Real.log 2 := by
    rw [div_le_div_iff₀ (by norm_num) hlog2pos]
    nlinarith [Real.log_two_lt_d9]
  rw [Real.log_mul (by norm_num) (ne_of_gt hXpos),
    show (1 / Real.log 2) * (Real.log 2 + Real.log X) =
      1 + (1 / Real.log 2) * Real.log X from by field_simp]
  linarith [mul_le_mul_of_nonneg_right hcoef hlogX]

/-- `∑_{d ≤ X} |gKernel d| · d/√d ≤ C₁ · log (2X)`. -/
lemma gKernel_sqrtnorm_partial_bound : ∃ C1 : ℝ, 0 < C1 ∧ ∀ X : ℕ,
      (∑ d ∈ Finset.Icc 1 X, |gKernel d| * (d : ℝ) / √d) ≤ C1 * Real.log (2 * X) := by
  obtain ⟨B, hBpos, hB⟩ := sqrtnorm_le_const_mul_totient_sum
  obtain ⟨A, hApos, hA⟩ := sum_recip_totient_le
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨B * A / Real.log 2, div_pos (mul_pos hBpos hApos) hlog2pos, ?_⟩
  intro X
  rcases Nat.eq_zero_or_pos X with hX0 | hXpos
  · subst hX0; simp
  · calc (∑ d ∈ Finset.Icc 1 X, |gKernel d| * (d : ℝ) / √d) ≤
        B * ∑ r ∈ Finset.Icc 1 (Nat.sqrt X), (1 : ℝ) / (r.totient : ℝ) := hB X
      _ ≤ B * (A * (1 + Real.log (Nat.sqrt X))) := mul_le_mul_of_nonneg_left (hA _) hBpos.le
      _ ≤ B * (A * ((1 / Real.log 2) * Real.log (2 * X))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (log_sqrt_arith_bound X hXpos) hApos.le) hBpos.le
      _ = B * A / Real.log 2 * Real.log (2 * X) := by ring

/-- `∑_{d ≤ X} |gKernel d| · d ≤ C_A · √X · log (2X)`, from `gKernel_sqrtnorm_partial_bound` and
`√d ≤ √X`. -/
lemma gKernel_partial_weighted_bound : ∃ CA : ℝ, 0 < CA ∧ ∀ X : ℕ,
      (∑ d ∈ Finset.Icc 1 X, |gKernel d| * (d : ℝ)) ≤ CA * √X * Real.log (2 * X) := by
  obtain ⟨C1, hC1pos, hC1⟩ := gKernel_sqrtnorm_partial_bound
  refine ⟨C1, hC1pos, ?_⟩
  intro X
  have hkey : ∀ d ∈ Finset.Icc 1 X, |gKernel d| * (d : ℝ) ≤
      √X * (|gKernel d| * (d : ℝ) / √d) := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hsd : (0 : ℝ) < √d := Real.sqrt_pos.mpr (by exact_mod_cast hd.1)
    calc |gKernel d| * (d : ℝ)
        = |gKernel d| * (d : ℝ) / √d * √d := by field_simp
      _ ≤ |gKernel d| * (d : ℝ) / √d * √X := by gcongr; exact_mod_cast hd.2
      _ = √X * (|gKernel d| * (d : ℝ) / √d) := by ring
  calc (∑ d ∈ Finset.Icc 1 X, |gKernel d| * (d : ℝ))
      ≤ ∑ d ∈ Finset.Icc 1 X, √X * (|gKernel d| * (d : ℝ) / √d) :=
        Finset.sum_le_sum hkey
    _ = √X * ∑ d ∈ Finset.Icc 1 X, (|gKernel d| * (d : ℝ) / √d) :=
        (Finset.mul_sum _ _ _).symm
    _ ≤ √X * (C1 * Real.log (2 * X)) :=
        mul_le_mul_of_nonneg_left (hC1 X) (Real.sqrt_nonneg _)
    _ = C1 * √X * Real.log (2 * X) := by ring

end PrimeGaps
