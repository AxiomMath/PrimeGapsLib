/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S2m.Error.WindowError

/-!
# Sums of the fourth power of the divisor function

The squarefree and squarefull decomposition and the resulting bounds on sums of
`tau r q ^ 4 / phi q`.

## Main results

* `exists_sqfree_sqfull_factor`
* `full_le_sqfree_mul_sqfull`
* `tau4_totient_full_sum_le`
-/

@[expose] public section

open PrimeGaps

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.zeta
open scoped Finset

namespace MaynardS2Error

open ArithmeticFunction zeta

/-- For squarefree `q`, `(τ r q) ^ 4 = (ζ ^ (r ^ 4)) q`. -/
lemma tau4_sqfree_eq_zeta (r q : ℕ) (hsq : Squarefree q) :
    (τ r q : ℝ) ^ 4 = ((ζ ^ (r ^ 4)) q : ℝ) := by
  have h : τ r q ^ 4 = (ζ ^ r ^ 4) q := by
    rw [show r ^ 4 = (r ^ 2) ^ 2 by ring,
      ← ArithmeticFunction.tau_sq_eq_tau_sq (n := q) (r := r ^ 2) hsq,
      ← ArithmeticFunction.tau_sq_eq_tau_sq (n := q) (r := r) hsq, ← pow_mul]
  exact_mod_cast h

/-- `∑_{u ≤ z} μ(u)² * τ r u ^ 4 / φ u ≤ C * Real.log z ^ (r ^ 4)` for `z ≥ 2`. -/
lemma tau4_totient_sqfree_sum_le (r : ℕ) (hr : 1 ≤ r) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      (∑ u ∈ Finset.Icc 1 ⌊z⌋₊,
        (μ u : ℝ) ^ 2 * (τ r u : ℝ) ^ 4 / (Nat.totient u : ℝ)) ≤
        C * (Real.log z) ^ (r ^ 4) := by
  obtain ⟨C, hCpos, hC⟩ := WeightedDivisorSum.weightedSum_le (r ^ 4) (Nat.one_le_pow _ _ hr)
  refine ⟨C, hCpos, fun z hz ↦ le_of_eq_of_le (Finset.sum_congr rfl fun u _ ↦ ?_) (hC z hz)⟩
  by_cases hsq : Squarefree u
  · rw [tau4_sqfree_eq_zeta r u hsq]
  · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; norm_num

/-- The multiplicative summand `g_r(q) = τ_r(q)⁴ / φ(q)`. -/
noncomputable def gFun (r q : ℕ) : ℝ := (τ r q : ℝ) ^ 4 / (Nat.totient q : ℝ)

/-- `0 ≤ gFun r q`. -/
lemma gFun_nonneg (r q : ℕ) : 0 ≤ gFun r q := by unfold gFun; positivity

/-- A positive integer is *squarefull* (powerful) if every prime in its factorization occurs with
exponent `≥ 2`. `1` is squarefull vacuously. -/
def Squarefull (w : ℕ) : Prop := 1 ≤ w ∧ ∀ p ∈ w.primeFactors, 2 ≤ w.factorization p

/-- `Squarefull` is decidable, being a bounded conjunction over `w.primeFactors`. -/
instance : DecidablePred Squarefull := fun w ↦ by unfold Squarefull; infer_instance

/-- Every squarefull `w` is of the form `a ^ 2 * b ^ 3` with `1 ≤ a` and `1 ≤ b`. -/
lemma sqfull_eq_sq_mul_cube (w : ℕ) (hw : Squarefull w) :
    ∃ a b : ℕ, 1 ≤ a ∧ 1 ≤ b ∧ w = a ^ 2 * b ^ 3 := by
  classical
  have hw0 : w ≠ 0 := Nat.one_le_iff_ne_zero.mp hw.1
  set f := w.factorization with hf
  have hmem : ∀ p ∈ f.support, p ∈ w.primeFactors := fun p hp ↦ by
    rwa [hf, Nat.support_factorization] at hp
  have hone : ∀ e : ℕ → ℕ, 1 ≤ ∏ p ∈ f.support, p ^ e p := fun e ↦
    Finset.one_le_prod' fun p hp ↦ Nat.one_le_pow _ _ (Nat.pos_of_mem_primeFactors (hmem p hp))
  refine ⟨∏ p ∈ f.support, p ^ ((f p - 3 * (f p % 2)) / 2),
          ∏ p ∈ f.support, p ^ (f p % 2), hone _, hone _, ?_⟩
  have hwexp : w = ∏ p ∈ f.support, p ^ f p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hw0]
    rw [Finsupp.prod]
  rw [hwexp, ← Finset.prod_pow, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p hp ↦ ?_
  rw [← pow_mul, ← pow_mul, ← pow_add]
  have hp2 : 2 ≤ f p := hw.2 p (hmem p hp)
  congr 1
  omega

/-- `τ 2 n = n.divisors.card`. -/
lemma tau_two_eq_card_divisors (n : ℕ) : (τ 2 n : ℝ) = (#n.divisors : ℝ) := by
  have hval : τ 2 n = #n.divisors := by
    rw [sq, ArithmeticFunction.zeta_mul_apply,
      Finset.sum_congr rfl fun i hi ↦ show ζ i = 1 by
        simp [(Nat.pos_of_mem_divisors hi).ne'],
      Finset.sum_const, smul_eq_mul, mul_one]
  exact_mod_cast hval

/-- For `δ > 0` there is `C > 0` with `gFun r n ≤ C * n ^ (-1 + δ)` for all `n ≥ 1`. -/
lemma gFun_le_rpow (r : ℕ) (δ : ℝ) (hδ0 : 0 < δ) : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n →
      gFun r n ≤ C * (n : ℝ) ^ (-(1 : ℝ) + δ) := by
  obtain ⟨C₁, hC₁pos, hτ⟩ := tau_le_rpow r (δ / 8) (by positivity)
  obtain ⟨C₂, hC₂pos, hd⟩ := tau_le_rpow 2 (δ / 2) (by positivity)
  refine ⟨C₁ ^ 4 * C₂, by positivity, ?_⟩
  intro n hn
  have hn0 : 0 < n := hn
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hτn := hτ n hn
  have hτnn : (0 : ℝ) ≤ (τ r n : ℝ) := by positivity
  have hdcardpos : 0 < #n.divisors := Finset.card_pos.mpr ⟨n, Nat.mem_divisors_self n hn0.ne'⟩
  have hdcardR : (0 : ℝ) < (#n.divisors : ℝ) := by exact_mod_cast hdcardpos
  have hdn : (#n.divisors : ℝ) ≤ C₂ * (n : ℝ) ^ (δ / 2) := by
    rw [← tau_two_eq_card_divisors n]
    exact hd n hn
  have hφge := Nat.div_card_le_totient n hn
  have hφpos : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn0
  have hτ4 : (τ r n : ℝ) ^ 4 ≤ C₁ ^ 4 * (n : ℝ) ^ (δ / 2) := by
    have hpow : ((n : ℝ) ^ (δ / 8)) ^ (4 : ℕ) = (n : ℝ) ^ (δ / 2) := by
      rw [← Real.rpow_natCast ((n : ℝ) ^ (δ / 8)) 4, ← Real.rpow_mul hnR.le]
      congr 1; ring
    calc (τ r n : ℝ) ^ 4 ≤ (C₁ * (n : ℝ) ^ (δ / 8)) ^ 4 := pow_le_pow_left₀ hτnn hτn 4
      _ = C₁ ^ 4 * (n : ℝ) ^ (δ / 2) := by rw [mul_pow, hpow]
  calc gFun r n ≤ (τ r n : ℝ) ^ 4 * (#n.divisors : ℝ) / (n : ℝ) := by
        unfold gFun
        rw [div_le_div_iff₀ hφpos hnR, mul_assoc]
        rw [div_le_iff₀ hdcardR] at hφge
        gcongr
        linarith
    _ ≤ (C₁ ^ 4 * (n : ℝ) ^ (δ / 2)) * (C₂ * (n : ℝ) ^ (δ / 2)) / (n : ℝ) := by
        rw [div_le_div_iff_of_pos_right hnR]
        exact mul_le_mul hτ4 hdn (by positivity) (by positivity)
    _ = C₁ ^ 4 * C₂ * (n : ℝ) ^ (-(1 : ℝ) + δ) := by
        rw [div_eq_iff hnR.ne', show - (1 : ℝ) + δ = δ / 2 + δ / 2 - 1 by ring,
          Real.rpow_sub hnR, Real.rpow_add hnR, Real.rpow_one]
        field_simp

/-- For `s > 1` the partial sums `∑_{n ≤ N} n ^ (-s)` are bounded uniformly in `N`. -/
lemma sum_rpow_neg_le (s : ℝ) (hs : 1 < s) :
    ∃ B : ℝ, 0 < B ∧ ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, (n : ℝ) ^ (-s)) ≤ B := by
  have hsum : Summable (fun n : ℕ ↦ (n : ℝ) ^ (-s)) :=
    ((Real.summable_nat_rpow_inv).mpr hs).congr fun n ↦ (Real.rpow_neg (by positivity) s).symm
  have hnonneg : ∀ n : ℕ, (0 : ℝ) ≤ (n : ℝ) ^ (-s) := fun n ↦ by positivity
  exact ⟨(∑' n : ℕ, (n : ℝ) ^ (-s)) + 1,
    by linarith [(tsum_nonneg hnonneg : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-s))],
    fun N ↦ by linarith [hsum.sum_le_tsum (Finset.Icc 1 N) fun i _ ↦ hnonneg i]⟩

/-- The squarefull sum `∑_{w ≤ N squarefull} gFun r w` is dominated by the double sum of
`gFun r (a ^ 2 * b ^ 3)` over `(a, b) ∈ Icc 1 N ×ˢ Icc 1 N`. -/
lemma sqfull_sum_le_prod_sum (r : ℕ) (N : ℕ) :
    (∑ w ∈ {w ∈ (Finset.Icc 1 N) | Squarefull w}, gFun r w) ≤
      ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), gFun r (p.1 ^ 2 * p.2 ^ 3) := by
  classical
  set S := {w ∈ (Finset.Icc 1 N) | Squarefull w} with hS
  set Φ : ℕ → ℕ × ℕ := fun w ↦ if h : Squarefull w then
      (Classical.choose (sqfull_eq_sq_mul_cube w h),
       Classical.choose (Classical.choose_spec (sqfull_eq_sq_mul_cube w h)))
    else (0, 0) with hΦ
  have hΦspec : ∀ w, Squarefull w →
      1 ≤ (Φ w).1 ∧ 1 ≤ (Φ w).2 ∧ w = (Φ w).1 ^ 2 * (Φ w).2 ^ 3 := fun w hw ↦ by
    simpa only [hΦ, dif_pos hw] using
      Classical.choose_spec (Classical.choose_spec (sqfull_eq_sq_mul_cube w hw))
  have hSmem : ∀ w ∈ S, 1 ≤ w ∧ w ≤ N ∧ Squarefull w := fun w hw ↦ by
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hw
    exact ⟨hw.1.1, hw.1.2, hw.2⟩
  have hΦbox : ∀ w ∈ S, Φ w ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) := by
    intro w hw
    obtain ⟨hw1, hwN, hwsf⟩ := hSmem w hw
    obtain ⟨ha1, hb1, hwab⟩ := hΦspec w hwsf
    have ha : (Φ w).1 ≤ w := Nat.le_of_dvd hw1 ⟨(Φ w).1 * (Φ w).2 ^ 3, hwab.trans (by ring)⟩
    have hb : (Φ w).2 ≤ w := Nat.le_of_dvd hw1 ⟨(Φ w).1 ^ 2 * (Φ w).2 ^ 2, hwab.trans (by ring)⟩
    exact Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨ha1, ha.trans hwN⟩,
      Finset.mem_Icc.2 ⟨hb1, hb.trans hwN⟩⟩
  have hΦinj : Set.InjOn Φ ↑S := fun w hw w' hw' heq ↦ by
    rw [(hΦspec w (hSmem w hw).2.2).2.2, (hΦspec w' (hSmem w' hw').2.2).2.2, heq]
  have hgeq : ∀ w ∈ S, gFun r w = gFun r ((Φ w).1 ^ 2 * (Φ w).2 ^ 3) := fun w hw ↦ by
    rw [← (hΦspec w (hSmem w hw).2.2).2.2]
  calc (∑ w ∈ S, gFun r w)
      = ∑ w ∈ S, gFun r ((Φ w).1 ^ 2 * (Φ w).2 ^ 3) := Finset.sum_congr rfl hgeq
    _ = ∑ p ∈ Finset.image Φ S, gFun r (p.1 ^ 2 * p.2 ^ 3) :=
        (Finset.sum_image (f := fun p : ℕ × ℕ ↦ gFun r (p.1 ^ 2 * p.2 ^ 3))
          (g := Φ) fun _ hx _ hy h ↦ hΦinj hx hy h).symm
    _ ≤ ∑ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), gFun r (p.1 ^ 2 * p.2 ^ 3) :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp ↦ by obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hp; exact hΦbox w hw)
          fun p _ _ ↦ gFun_nonneg r _

/-- The squarefull sums `∑_{w ≤ N squarefull} gFun r w` are bounded by a constant `K`
independent of `N`. -/
lemma sqfull_g_sum_le_const (r : ℕ) : ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ,
      (∑ w ∈ {w ∈ (Finset.Icc 1 N) | Squarefull w}, gFun r w) ≤ K := by
  obtain ⟨C, hCpos, hgbd⟩ := gFun_le_rpow r (1 / 6) (by norm_num)
  obtain ⟨B₁, hB₁pos, hB₁⟩ := sum_rpow_neg_le (5 / 3) (by norm_num)
  obtain ⟨B₂, hB₂pos, hB₂⟩ := sum_rpow_neg_le (5 / 2) (by norm_num)
  refine ⟨C * B₁ * B₂, by positivity, fun N ↦ (sqfull_sum_le_prod_sum r N).trans ?_⟩
  have hterm : ∀ p ∈ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N), gFun r (p.1 ^ 2 * p.2 ^ 3) ≤
        C * ((p.1 : ℝ) ^ (-(5 / 3 : ℝ)) * (p.2 : ℝ) ^ (-(5 / 2 : ℝ))) := by
    intro p hp
    rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc] at hp
    obtain ⟨⟨ha1, -⟩, hb1, -⟩ := hp
    have ha0 : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast ha1
    have hb0 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast hb1
    have hbd := hgbd (p.1 ^ 2 * p.2 ^ 3) (Nat.mul_pos (Nat.pow_pos ha1) (Nat.pow_pos hb1))
    rwa [show ((p.1 ^ 2 * p.2 ^ 3 : ℕ) : ℝ) = (p.1 : ℝ) ^ 2 * (p.2 : ℝ) ^ 3 by push_cast; ring,
      Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (p.1 : ℝ) 2,
      ← Real.rpow_natCast (p.2 : ℝ) 3, ← Real.rpow_mul ha0.le, ← Real.rpow_mul hb0.le,
      show ((2 : ℕ) : ℝ) * (-(1 : ℝ) + 1 / 6) = -(5 / 3 : ℝ) by norm_num,
      show ((3 : ℕ) : ℝ) * (-(1 : ℝ) + 1 / 6) = -(5 / 2 : ℝ) by norm_num] at hbd
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum]
  simp only [Finset.sum_product]
  rw [← Finset.sum_mul_sum, show C * B₁ * B₂ = C * (B₁ * B₂) by ring]
  gcongr
  exacts [hB₁ N, hB₂ N]

/-- `τ r (a * b) = τ r a * τ r b` for coprime `a, b`. -/
lemma tau_mul_coprime (r a b : ℕ) (hcop : Nat.Coprime a b) : τ r (a * b) = τ r a * τ r b :=
  ArithmeticFunction.isMultiplicative_tau.map_mul_of_coprime hcop

/-- `gFun r (a * b) = gFun r a * gFun r b` for coprime positive `a, b`. -/
lemma gFun_mul_coprime (r a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) (hcop : Nat.Coprime a b) :
    gFun r (a * b) = gFun r a * gFun r b := by
  unfold gFun
  rw [tau_mul_coprime r a b hcop, Nat.totient_mul hcop]
  have hφa : (0 : ℝ) < (a.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr ha
  have hφb : (0 : ℝ) < (b.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hb
  push_cast
  rw [mul_pow]
  field_simp

/-- Every `q ≥ 1` factors as `q = u * w` with `u` squarefree, `w` squarefull and `(u, w) = 1`. -/
lemma exists_sqfree_sqfull_factor (q : ℕ) (hq : 1 ≤ q) :
    ∃ u w : ℕ, Squarefree u ∧ Squarefull w ∧ Nat.Coprime u w ∧ q = u * w := by
  classical
  have hq0 : q ≠ 0 := Nat.one_le_iff_ne_zero.mp hq
  set f := q.factorization with hf
  set U := f.support.filter (fun p ↦ f p = 1) with hU
  set W := f.support.filter (fun p ↦ ¬ f p = 1) with hW
  have hprime : ∀ p ∈ f.support, p.Prime := fun p hp ↦
    Nat.prime_of_mem_primeFactors (by rwa [hf, Nat.support_factorization] at hp)
  have hcopp : ∀ p ∈ f.support, ∀ p' ∈ f.support, p ≠ p' → Nat.Coprime p p' :=
    fun p hp p' hp' hne ↦ (Nat.coprime_primes (hprime p hp) (hprime p' hp')).mpr hne
  have hWmem : ∀ p ∈ W, p.Prime ∧ 2 ≤ f p := by
    intro p hp
    simp only [hW, Finset.mem_filter] at hp
    have := Finsupp.mem_support_iff.mp hp.1
    exact ⟨hprime p hp.1, by omega⟩
  refine ⟨∏ p ∈ U, p ^ f p, ∏ p ∈ W, p ^ f p, ?_, ?_, ?_, ?_⟩
  · refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp p' hp' hne ↦ ?_) fun p hp ↦ ?_
    · simp only [hU, Finset.mem_coe, Finset.mem_filter] at hp hp'
      exact Nat.coprime_iff_isRelPrime.mp (Nat.Coprime.pow _ _ (hcopp p hp.1 p' hp'.1 hne))
    · simp only [hU, Finset.mem_filter] at hp
      rw [hp.2, pow_one]
      exact (hprime p hp.1).squarefree
  · refine ⟨Finset.one_le_prod' fun p hp ↦ Nat.one_le_pow _ _ (hWmem p hp).1.pos, fun p hp ↦ ?_⟩
    obtain ⟨hpp, -, hne0⟩ := Nat.mem_primeFactors.mp hp
    have hpW : p ∈ W := by
      obtain ⟨p', hp'W, hp'dvd⟩ :=
        (Prime.dvd_finsetProd_iff hpp.prime _).mp (Nat.dvd_of_mem_primeFactors hp)
      rwa [(Nat.prime_dvd_prime_iff_eq hpp (hWmem p' hp'W).1).mp (hpp.dvd_of_dvd_pow hp'dvd)]
    rw [← Nat.Prime.pow_dvd_iff_le_factorization hpp hne0]
    exact (pow_dvd_pow p (hWmem p hpW).2).trans (Finset.dvd_prod_of_mem _ hpW)
  · refine Nat.Coprime.prod_left fun p hp ↦ Nat.Coprime.prod_right fun p' hp' ↦ ?_
    simp only [hU, Finset.mem_filter] at hp
    simp only [hW, Finset.mem_filter] at hp'
    exact Nat.Coprime.pow _ _ (hcopp p hp.1 p' hp'.1 fun heq ↦ hp'.2 (heq ▸ hp.2))
  · have hqexp : q = ∏ p ∈ f.support, p ^ f p := by
      conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hq0]
      rw [Finsupp.prod]
    rw [hqexp, hU, hW]
    exact (Finset.prod_filter_mul_prod_filter_not f.support (fun p ↦ f p = 1) _).symm

/-- The full sum of `gFun r` over `Icc 1 M` factors through `exists_sqfree_sqfull_factor`: it is at
most the squarefree sum times the squarefull sum. -/
lemma full_le_sqfree_mul_sqfull (r : ℕ) (M : ℕ) : (∑ q ∈ Finset.Icc 1 M, gFun r q) ≤
      (∑ u ∈ {u ∈ (Finset.Icc 1 M) | Squarefree u}, gFun r u) *
          (∑ w ∈ {w ∈ (Finset.Icc 1 M) | Squarefull w}, gFun r w) := by
  classical
  set A := Finset.Icc 1 M with hA
  set U := {u ∈ (Finset.Icc 1 M) | Squarefree u} with hUdef
  set W := {w ∈ (Finset.Icc 1 M) | Squarefull w} with hWdef
  set Ψ : ℕ → ℕ × ℕ := fun q ↦ if h : 1 ≤ q then
      (Classical.choose (exists_sqfree_sqfull_factor q h),
       Classical.choose (Classical.choose_spec (exists_sqfree_sqfull_factor q h)))
    else (1, 1) with hΨ
  have hΨspec : ∀ q, 1 ≤ q → Squarefree (Ψ q).1 ∧ Squarefull (Ψ q).2 ∧
        Nat.Coprime (Ψ q).1 (Ψ q).2 ∧ q = (Ψ q).1 * (Ψ q).2 := fun q hq ↦ by
    simpa only [hΨ, dif_pos hq] using
      Classical.choose_spec (Classical.choose_spec (exists_sqfree_sqfull_factor q hq))
  have hAmem : ∀ q ∈ A, 1 ≤ q ∧ q ≤ M := fun q hq ↦ by rwa [hA, Finset.mem_Icc] at hq
  have hΨpos : ∀ q ∈ A, 1 ≤ (Ψ q).1 ∧ 1 ≤ (Ψ q).2 := fun q hq ↦ by
    obtain ⟨hsf, hsfull, -, -⟩ := hΨspec q (hAmem q hq).1
    exact ⟨Nat.pos_of_ne_zero fun h0 ↦ not_squarefree_zero (h0 ▸ hsf), hsfull.1⟩
  have hΨbox : ∀ q ∈ A, Ψ q ∈ U ×ˢ W := by
    intro q hq
    obtain ⟨hq1, hqM⟩ := hAmem q hq
    obtain ⟨hu1, hw1⟩ := hΨpos q hq
    obtain ⟨hsf, hsfull, -, hqeq⟩ := hΨspec q hq1
    have hule : (Ψ q).1 ≤ q := Nat.le_of_dvd hq1 ⟨(Ψ q).2, hqeq⟩
    have hwle : (Ψ q).2 ≤ q := Nat.le_of_dvd hq1 ⟨(Ψ q).1, hqeq.trans (Nat.mul_comm _ _)⟩
    rw [hUdef, hWdef, Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hu1, hule.trans hqM⟩, hsf⟩, ⟨⟨hw1, hwle.trans hqM⟩, hsfull⟩⟩
  have hΨinj : Set.InjOn Ψ ↑A := fun q hq q' hq' heq ↦ by
    rw [(hΨspec q (hAmem q hq).1).2.2.2, (hΨspec q' (hAmem q' hq').1).2.2.2, heq]
  have hgeq : ∀ q ∈ A, gFun r q = gFun r (Ψ q).1 * gFun r (Ψ q).2 := fun q hq ↦ by
    conv_lhs => rw [(hΨspec q (hAmem q hq).1).2.2.2]
    exact gFun_mul_coprime r (Ψ q).1 (Ψ q).2 (hΨpos q hq).1 (hΨpos q hq).2
      (hΨspec q (hAmem q hq).1).2.2.1
  calc (∑ q ∈ A, gFun r q) = ∑ q ∈ A, gFun r (Ψ q).1 * gFun r (Ψ q).2 := Finset.sum_congr rfl hgeq
    _ = ∑ p ∈ Finset.image Ψ A, gFun r p.1 * gFun r p.2 :=
        (Finset.sum_image (f := fun p : ℕ × ℕ ↦ gFun r p.1 * gFun r p.2)
          (g := Ψ) fun _ hx _ hy h ↦ hΨinj hx hy h).symm
    _ ≤ ∑ p ∈ U ×ˢ W, gFun r p.1 * gFun r p.2 :=
        Finset.sum_le_sum_of_subset_of_nonneg
          (fun p hp ↦ by obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hp; exact hΨbox q hq)
          fun p _ _ ↦ mul_nonneg (gFun_nonneg r _) (gFun_nonneg r _)
    _ = (∑ u ∈ U, gFun r u) * (∑ w ∈ W, gFun r w) := by
        rw [Finset.sum_mul_sum, Finset.sum_product]

/-- `∑_{u ≤ z squarefree} gFun r u ≤ C * Real.log z ^ (r ^ 4)` for `z ≥ 2`. -/
lemma sqfree_g_sum_le (r : ℕ) (hr : 1 ≤ r) : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      (∑ u ∈ {u ∈ (Finset.Icc 1 ⌊z⌋₊) | Squarefree u}, gFun r u) ≤
        C * (Real.log z) ^ (r ^ 4) := by
  obtain ⟨C, hCpos, hC⟩ := tau4_totient_sqfree_sum_le r hr
  refine ⟨C, hCpos, fun z hz ↦ le_of_eq_of_le ?_ (hC z hz)⟩
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  by_cases hsq : Squarefree u
  · have hm2 : (μ u : ℝ) ^ 2 = 1 := by
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsq
    rw [if_pos hsq, hm2]; unfold gFun; ring
  · rw [if_neg hsq, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsq]; norm_num

/-- `∑_{q ≤ z} τ r q ^ 4 / φ q ≤ C * Real.log z ^ B` for `z ≥ 2`, with no squarefreeness gate. -/
lemma tau4_totient_full_sum_le (r : ℕ) (hr : 1 ≤ r) : ∃ (C B : ℝ), 0 < C ∧ ∀ z : ℝ, 2 ≤ z →
      (∑ q ∈ (Finset.Icc 1 ⌊z⌋₊),
        (τ r q : ℝ) ^ 4 / (Nat.totient q : ℝ)) ≤ C * (Real.log z) ^ B := by
  obtain ⟨C₀, hC₀pos, hE⟩ := sqfree_g_sum_le r hr
  obtain ⟨K, hKpos, hF⟩ := sqfull_g_sum_le_const r
  refine ⟨C₀ * K, (r : ℝ) ^ 4, by positivity, fun z hz ↦ ?_⟩
  have hexp : (Real.log z) ^ (r ^ 4) = (Real.log z) ^ ((r : ℝ) ^ 4) := by
    rw [← Real.rpow_natCast (Real.log z) (r ^ 4)]
    congr 1
    push_cast; ring
  calc (∑ q ∈ Finset.Icc 1 ⌊z⌋₊, (τ r q : ℝ) ^ 4 / (Nat.totient q : ℝ))
      ≤ (∑ u ∈ {u ∈ (Finset.Icc 1 ⌊z⌋₊) | Squarefree u}, gFun r u) *
          (∑ w ∈ {w ∈ (Finset.Icc 1 ⌊z⌋₊) | Squarefull w}, gFun r w) :=
        full_le_sqfree_mul_sqfull r ⌊z⌋₊
    _ ≤ (C₀ * (Real.log z) ^ (r ^ 4)) * K :=
        mul_le_mul (hE z hz) (hF ⌊z⌋₊) (Finset.sum_nonneg fun w _ ↦ gFun_nonneg r w)
          (mul_nonneg hC₀pos.le (pow_nonneg (Real.log_nonneg (by linarith)) _))
    _ = C₀ * K * (Real.log z) ^ ((r : ℝ) ^ 4) := by rw [hexp]; ring

end MaynardS2Error
