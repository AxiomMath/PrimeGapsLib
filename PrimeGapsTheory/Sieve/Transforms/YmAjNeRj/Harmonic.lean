/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Transforms.YmAjNeRj.Kernel

import PrimeGapsTheory.ArithmeticFunction.Estimates

/-!
# Coprime harmonic sums

The Euler-factor product and the coprime harmonic and `sumA` bounds.

## Main results

* `sumA_le`
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius

open scoped ArithmeticFunction.detotient

namespace PrimeGaps

open scoped ArithmeticFunction BigOperators

namespace MaynardOffDiagonal

open ArithmeticFunction (moebius)

noncomputable section


/-- **The sieve modulus is eventually smaller than `log (N ^ a)`.**  For any `a > 0` there is a
threshold `N₀ ≥ 3` beyond which `primorial ⌊D₀ N⌋₊ ≤ log (N ^ a)`: the primorial is at most
`4 ^ ⌊D₀ N⌋₊ ≤ (log log N) ^ 2`, and `(log log N) ^ 2 ≤ a * log N = log (N ^ a)` eventually. -/
private theorem primorial_D0_le_log_rpow (a : ℝ) (ha : 0 < a) : ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      0 < N ∧ (primorial ⌊D₀ N⌋₊ : ℝ) ≤ Real.log (N ^ a) := by
  have hgrow : ∀ᶠ m in Filter.atTop, (Real.log m) ^ 2 ≤ a * m := by
    have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 (by norm_num)
    simp only [one_mul, add_zero] at h
    filter_upwards [h.eventually (eventually_lt_nhds ha), Filter.eventually_gt_atTop (0 : ℝ)]
      with m hm hmpos
    rw [div_lt_iff₀ hmpos] at hm
    linarith
  rw [Filter.eventually_atTop] at hgrow
  obtain ⟨m₁, hm₁⟩ := hgrow
  refine ⟨max 3 (rexp (max m₁ (rexp 1))), le_max_left _ _, ?_⟩
  intro N hN
  have hNexp : rexp (max m₁ (rexp 1)) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : 0 < N := lt_of_lt_of_le (Real.exp_pos _) hNexp
  refine ⟨hNpos, ?_⟩
  have hlogN : max m₁ (rexp 1) ≤ Real.log N := (Real.le_log_iff_exp_le hNpos).mpr hNexp
  have hlogN_ge_e : rexp 1 ≤ Real.log N := le_trans (le_max_right _ _) hlogN
  have hlogN_ge_m1 : m₁ ≤ Real.log N := le_trans (le_max_left _ _) hlogN
  have hLpos : 0 < Real.log N := lt_of_lt_of_le (Real.exp_pos _) hlogN_ge_e
  have hLL : 1 ≤ Real.log (Real.log N) := (Real.le_log_iff_exp_le hLpos).mpr hlogN_ge_e
  have hWbound : (primorial ⌊D₀ N⌋₊ : ℝ) ≤ (Real.log (Real.log N)) ^ (2 : ℝ) := by
    set L := Real.log (Real.log N)
    have hfloor : (⌊D₀ N⌋₊ : ℝ) ≤ Real.log L := by
      rw [show D₀ N = Real.log L from rfl]; exact Nat.floor_le (Real.log_nonneg hLL)
    calc (primorial ⌊D₀ N⌋₊ : ℝ) ≤ (4 : ℝ) ^ (⌊D₀ N⌋₊ : ℕ) := by
          exact_mod_cast primorial_le_four_pow ⌊D₀ N⌋₊
      _ = (4 : ℝ) ^ ((⌊D₀ N⌋₊ : ℕ) : ℝ) := by rw [Real.rpow_natCast]
      _ ≤ (4 : ℝ) ^ (Real.log L) := Real.rpow_le_rpow_of_exponent_le (by norm_num) hfloor
      _ = L ^ (Real.log 4) := by
          rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 4),
              Real.rpow_def_of_pos (by linarith : (0 : ℝ) < L)]; ring_nf
      _ ≤ L ^ (2 : ℝ) := by
          refine Real.rpow_le_rpow_of_exponent_le hLL ?_
          rw [Real.log_le_iff_le_exp (by norm_num), show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
          nlinarith [Real.add_one_le_exp (1 : ℝ), Real.exp_pos (1 : ℝ)]
  rw [Real.log_rpow hNpos]
  calc (primorial ⌊D₀ N⌋₊ : ℝ) ≤ (Real.log (Real.log N)) ^ (2 : ℝ) := hWbound
    _ = (Real.log (Real.log N)) ^ 2 := by
        rw [← Real.rpow_natCast (Real.log (Real.log N)) 2]; norm_num
    _ ≤ a * Real.log N := hm₁ _ hlogN_ge_m1

/-- Smoothness of the sieve modulus: for all large `N`, every prime factor of
`primorial ⌊D₀ N⌋₊` is at most `N ^ (θ / 2 - δ)`. -/
theorem primorial_D0_primeFactors_le_Rval (θ δ : ℝ) (hexp : 0 < θ / 2 - δ) :
    ∃ N₁ : ℝ, 3 ≤ N₁ ∧ ∀ N : ℝ, N₁ ≤ N →
      ∀ p ∈ (primorial ⌊D₀ N⌋₊).primeFactors, (p : ℝ) ≤ N ^ (θ / 2 - δ) := by
  obtain ⟨N₁, hN₁, hkey⟩ := primorial_D0_le_log_rpow (θ / 2 - δ) hexp
  refine ⟨N₁, hN₁, ?_⟩
  intro N hN p hp
  obtain ⟨hNpos, hWle⟩ := hkey N hN
  calc (p : ℝ) ≤ (primorial ⌊D₀ N⌋₊ : ℝ) := by
        exact_mod_cast Nat.le_of_dvd (primorial_pos _) (Nat.dvd_of_mem_primeFactors hp)
    _ ≤ Real.log (N ^ (θ / 2 - δ)) := hWle
    _ ≤ N ^ (θ / 2 - δ) :=
        le_trans (Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hNpos _)) (by linarith)

/-- `sumA W R ≤ momentSum W ⌊R⌋₊ * coprimeReciprocalSum W R`, by factoring
`1 / φ(n) = ∑_{de = n} μ(d)² / (φ(d) d) · 1 / e`. -/
theorem sumA_le_momentSum_mul_coprimeReciprocalSum (W : ℕ) (R : ℝ) :
    sumA W R ≤ momentSum W ⌊R⌋₊ * coprimeReciprocalSum W R := by
  classical
  set F : ℕ × ℕ → ℝ := fun p ↦
    ((μ p.1 : ℝ) ^ 2 / (Nat.totient p.1 : ℝ) * (1 / (p.1 : ℝ))) * (1 / (p.2 : ℝ)) with hF
  set momIdx := {d ∈ (Finset.Icc 1 ⌊R⌋₊) | Squarefree d ∧ Nat.gcd d W = 1} with hmomIdx
  set harIdx := {m ∈ (Finset.Icc 1 ⌊R⌋₊) | Nat.gcd m W = 1} with hharIdx
  have hFnn : ∀ p : ℕ × ℕ, 0 ≤ F p := fun p ↦ by rw [hF]; positivity
  have hper : ∀ n ∈ Sset W R, (1 / (Nat.totient n : ℝ)) = ∑ p ∈ n.divisorsAntidiagonal, F p := by
    intro n hn
    rw [Sset, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, _⟩, _, _⟩ := hn
    have hn0 : n ≠ 0 := by omega
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    rw [Nat.sum_divisorsAntidiagonal (f := fun a b ↦ F (a,b))]
    have hstep : ∀ e ∈ n.divisors, F (e, n / e) =
        ((μ e : ℝ) ^ 2 / (Nat.totient e : ℝ)) * (1 / (n : ℝ)) := by
      intro e he
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp he
      have he0' : (e : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr fun h ↦ hn0 (zero_dvd_iff.mp (h ▸ hdvd))
      have hecn : (e : ℝ) * ((n / e : ℕ) : ℝ) =
        (n : ℝ) := by exact_mod_cast Nat.mul_div_cancel' hdvd
      have hc0 : ((n / e : ℕ) : ℝ) ≠ 0 := fun h ↦ hnpos.ne' (by rw [← hecn, h, mul_zero])
      simp only [hF]
      field_simp
      rw [← hecn]; ring
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul,
      ArithmeticFunction.sum_moebius_sq_div_totient (α := ℝ)]
    field_simp
  have hdisj : (↑(Sset W R) : Set ℕ).PairwiseDisjoint (fun n ↦ n.divisorsAntidiagonal) := by
    intro a _ b _ hab
    simp only [Function.onFun, Finset.disjoint_left, Nat.mem_divisorsAntidiagonal]
    exact fun p hpa hpb ↦ hab (hpa.1.symm.trans hpb.1)
  have hsumA : sumA W R = ∑ p ∈ (Sset W R).biUnion (fun n ↦ n.divisorsAntidiagonal), F p := by
    rw [sumA, Finset.sum_congr rfl hper, ← Finset.sum_biUnion hdisj]
  have hsub : ((Sset W R).biUnion (fun n ↦ n.divisorsAntidiagonal)) ⊆ momIdx ×ˢ harIdx := by
    intro p hp
    rw [Finset.mem_biUnion] at hp
    obtain ⟨n, hn, hpn⟩ := hp
    rw [Sset, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨hn1, hnR⟩, hsq, hcop⟩ := hn
    rw [Nat.mem_divisorsAntidiagonal] at hpn
    obtain ⟨hmul, hn0⟩ := hpn
    have hd_dvd : p.1 ∣ n := ⟨p.2, hmul.symm⟩
    have hm_dvd : p.2 ∣ n := ⟨p.1, by rw [← hmul]; ring⟩
    have hd_pos : 1 ≤ p.1 := Nat.pos_of_ne_zero fun h ↦ hn0 (by rw [← hmul, h, zero_mul])
    have hm_pos : 1 ≤ p.2 := Nat.pos_of_ne_zero fun h ↦ hn0 (by rw [← hmul, h, mul_zero])
    rw [hmomIdx, hharIdx, Finset.mem_product, Finset.mem_filter, Finset.mem_filter,
      Finset.mem_Icc, Finset.mem_Icc]
    exact ⟨⟨⟨hd_pos, le_trans (Nat.le_of_dvd (by omega) hd_dvd) hnR⟩,
        hsq.squarefree_of_dvd hd_dvd, Nat.Coprime.coprime_dvd_left hd_dvd hcop⟩,
      ⟨hm_pos, le_trans (Nat.le_of_dvd (by omega) hm_dvd) hnR⟩,
      Nat.Coprime.coprime_dvd_left hm_dvd hcop⟩
  have hbound : ∑ p ∈ (Sset W R).biUnion (fun n ↦ n.divisorsAntidiagonal), F p ≤
      ∑ p ∈ momIdx ×ˢ harIdx, F p :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ ↦ hFnn i)
  have hprod : ∑ p ∈ momIdx ×ˢ harIdx, F p = momentSum W ⌊R⌋₊ * coprimeReciprocalSum W R := by
    simp only [hF]
    rw [Finset.sum_product, momentSum, coprimeReciprocalSum, Finset.sum_mul_sum]
  rw [hsumA]
  exact hbound.trans hprod.le

/-- `momentSum W N` is bounded by an absolute constant, uniformly in `W` and `N`. -/
theorem moment_sum_le : ∃ K : ℝ, 0 < K ∧ ∀ (W : ℕ) (N : ℕ), momentSum W N ≤ K := by
  classical
  set f : ℕ → ℝ := fun s ↦ (μ s : ℝ) ^ 2 / (Nat.totient s : ℝ) ^ 2 with hf
  have hsum : Summable f := lem_convergent_sum_phi
  have hfnn : ∀ s, 0 ≤ f s := by intro s; rw [hf]; positivity
  refine ⟨∑' s, f s, ?_, ?_⟩
  · have h1 : f 1 ≤ ∑' s, f s := hsum.le_tsum 1 (fun i _ ↦ hfnn i)
    rw [show f 1 = 1 by rw [hf]; simp] at h1; linarith
  · intro W N
    rw [momentSum]
    set S := {d ∈ (Finset.Icc 1 N) | Squarefree d ∧ Nat.gcd d W = 1} with hS
    have hterm : ∀ d ∈ S, (μ d : ℝ) ^ 2 / (Nat.totient d : ℝ) * (1 / (d : ℝ)) ≤ f d := by
      intro d hd
      rw [hS, Finset.mem_filter, Finset.mem_Icc] at hd
      obtain ⟨⟨hd1, -⟩, -, -⟩ := hd
      have hphir : (0 : ℝ) < (d.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hd1
      have hphile : (d.totient : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.totient_le d
      simp only [hf]
      rw [mul_one_div, div_div, sq]
      gcongr
      · exact mul_self_nonneg _
      · rw [sq]; exact mul_le_mul_of_nonneg_left hphile hphir.le
    exact (Finset.sum_le_sum hterm).trans (hsum.sum_le_tsum S (fun i _ ↦ hfnn i))

/-- **Splitting the coprimality-restricted Euler product.**  Over any range of primes containing
every prime factor of `W`, the local factors at primes dividing `W` are trivial, and reinstating
them turns the restricted product into `φ(W)/W` times the unrestricted one. -/
private theorem prod_coprime_euler_factor_eq (W : ℕ) (hW0 : W ≠ 0) (M : ℕ)
    (hsub : W.primeFactors ⊆ M.primesBelow) :
    (∏ p ∈ M.primesBelow, (1 - if Nat.Coprime p W then (1 / (p : ℝ)) else 0)⁻¹) =
      (Nat.totient W : ℝ) / (W : ℝ) * ∏ p ∈ M.primesBelow, (1 - 1 / (p : ℝ))⁻¹ := by
  classical
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hW0
  have hfac : ∀ p ∈ M.primesBelow, (1 - if Nat.Coprime p W then (1 / (p : ℝ)) else 0)⁻¹ =
        if p ∣ W then 1 else (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primesBelow hp
    by_cases hd : p ∣ W
    · rw [if_neg fun hc ↦ (Nat.Prime.coprime_iff_not_dvd hpp).mp hc hd, if_pos hd]; norm_num
    · rw [if_pos ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hd), if_neg hd]
  rw [Finset.prod_congr rfl hfac]
  rw [← Finset.prod_filter_mul_prod_filter_not M.primesBelow (fun p ↦ p ∣ W)]
  have hfirst : (∏ p ∈ M.primesBelow.filter (fun p ↦ p ∣ W),
      if p ∣ W then (1 : ℝ) else (1 - 1 / (p : ℝ))⁻¹) = 1 :=
    Finset.prod_eq_one fun p hp ↦ if_pos (Finset.mem_filter.mp hp).2
  rw [hfirst, one_mul]
  have hsecond : (∏ p ∈ M.primesBelow.filter (fun p ↦ ¬ p ∣ W),
        if p ∣ W then (1 : ℝ) else (1 - 1 / (p : ℝ))⁻¹) =
      ∏ p ∈ M.primesBelow.filter (fun p ↦ ¬ p ∣ W), (1 - 1 / (p : ℝ))⁻¹ :=
    Finset.prod_congr rfl fun p hp ↦ if_neg (Finset.mem_filter.mp hp).2
  rw [hsecond]
  have hsetW : M.primesBelow.filter (fun p ↦ p ∣ W) = W.primeFactors := by
    ext p
    rw [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors]
    exact ⟨fun ⟨⟨_, hpp⟩, hd⟩ ↦ ⟨hpp, hd, hW0⟩, fun ⟨hpp, hd, hne⟩ ↦
      ⟨Nat.mem_primesBelow.mp (hsub (Nat.mem_primeFactors.mpr ⟨hpp, hd, hne⟩)), hd⟩⟩
  rw [← Finset.prod_filter_mul_prod_filter_not M.primesBelow (fun p ↦ p ∣ W)
    (fun p ↦ (1 - 1 / (p : ℝ))⁻¹)]
  rw [hsetW]
  have hphi : (Nat.totient W : ℝ) / (W : ℝ) = ∏ p ∈ W.primeFactors, (1 - 1 / (p : ℝ)) := by
    have hr := congrArg (fun q : ℚ ↦ (q : ℝ)) (Nat.totient_eq_mul_prod_factors W)
    push_cast [one_div] at hr
    rw [hr, mul_comm, mul_div_assoc, div_self (ne_of_gt hWpos), mul_one]
    simp only [one_div]
  rw [hphi, ← mul_assoc, ← Finset.prod_mul_distrib]
  have hcancel : ∀ p ∈ W.primeFactors, (1 - 1 / (p : ℝ)) * (1 - 1 / (p : ℝ))⁻¹ = 1 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have h1 : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; linarith
    exact mul_inv_cancel₀ (by linarith)
  rw [Finset.prod_congr rfl hcancel, Finset.prod_const_one, one_mul]


/-- `∑_{m ≤ x, (m, W) = 1} 1/m ≤ C_H · (φ(W)/W) · (log x + 1)` for `x` -smooth `W`, with `C_H`
absolute. -/
theorem coprime_harmonic_le : ∃ C_H : ℝ, 0 < C_H ∧ ∀ (W : ℕ) (x : ℝ), 1 ≤ W → 1 ≤ x →
      (∀ p ∈ W.primeFactors, (p : ℝ) ≤ x) →
        coprimeReciprocalSum W x ≤ C_H * (Nat.totient W : ℝ) / (W : ℝ) * (Real.log x + 1) := by
  classical
  obtain ⟨D, hDpos, hD⟩ := WeightedDivisorSum.exp_sum_inv_pred_prime_le 1 (le_refl 1)
  refine ⟨max D 1, lt_of_lt_of_le hDpos (le_max_left _ _), ?_⟩
  intro W x hW hx hsmooth
  have hW0 : W ≠ 0 := by omega
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg hx
  have hdens_nn : (0 : ℝ) ≤ (Nat.totient W : ℝ) / (W : ℝ) := by positivity
  set f : ℕ →* ℝ := {
    toFun := fun n ↦ if Nat.Coprime n W then (1 / (n : ℝ)) else 0
    map_one' := by simp
    map_mul' := fun a b ↦ by
      by_cases ha : Nat.Coprime a W
      · by_cases hb : Nat.Coprime b W
        · rw [if_pos (Nat.Coprime.mul_left ha hb), if_pos ha, if_pos hb]
          push_cast; rw [one_div, one_div, one_div, mul_inv]
        · rw [if_neg fun h ↦ hb (Nat.Coprime.coprime_dvd_left ⟨a, by ring⟩ h), if_neg hb, mul_zero]
      · rw [if_neg fun h ↦ ha (Nat.Coprime.coprime_dvd_left ⟨b, rfl⟩ h), if_neg ha, zero_mul] }
  have hfapp : ∀ n, f n = if Nat.Coprime n W then (1 / (n : ℝ)) else 0 := fun n ↦ rfl
  have hfnn : ∀ n : ℕ, 0 ≤ f n := fun n ↦ by rw [hfapp]; split <;> simp
  set N := ⌊x⌋₊ + 1 with hN
  have hf1 : ∀ {p : ℕ}, Nat.Prime p → ‖f p‖ < 1 := by
    intro p hp
    rw [hfapp]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    by_cases h : Nat.Coprime p W
    · rw [if_pos h, Real.norm_eq_abs, abs_of_nonneg (by positivity), div_lt_one (by linarith)]
      linarith
    · rw [if_neg h]; simp
  obtain ⟨-, hhas⟩ :=
    EulerProduct.summable_and_hasSum_smoothNumbers_prod_primesBelow_geometric hf1 N
  have hval : ∑' (m : N.smoothNumbers), f m = ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ := hhas.tsum_eq
  have hsummable' : Summable (fun m : N.smoothNumbers ↦ f m) := hhas.summable
  have hdom : coprimeReciprocalSum W x ≤ ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ := by
    have hqnn : ∀ n, 0 ≤ N.smoothNumbers.indicator f n := fun n ↦
      Set.indicator_apply_nonneg fun _ ↦ hfnn n
    have hqsum : Summable (N.smoothNumbers.indicator f) :=
      summable_subtype_iff_indicator.mp hsummable'
    have heq : ∀ m ∈ {m ∈ (Finset.Icc 1 ⌊x⌋₊) | Nat.gcd m W = 1},
        (1 / (m : ℝ)) = N.smoothNumbers.indicator f m := by
      intro m hm
      rw [Finset.mem_filter, Finset.mem_Icc] at hm
      obtain ⟨⟨hm1, hmx⟩, hcop⟩ := hm
      have hsm : m ∈ N.smoothNumbers :=
        Nat.mem_smoothNumbers.mpr ⟨by omega, fun p hp ↦ by
          have := Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_primeFactorsList hp); omega⟩
      rw [Set.indicator_apply, if_pos hsm, hfapp, if_pos hcop]
    rw [← hval, tsum_subtype]
    unfold coprimeReciprocalSum
    rw [Finset.sum_congr rfl heq]
    exact hqsum.sum_le_tsum _ (fun i _ ↦ hqnn i)
  have hfact : ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ =
      (Nat.totient W : ℝ) / (W : ℝ) * ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ))⁻¹ := by
    have hsub : W.primeFactors ⊆ N.primesBelow := by
      intro p hp
      rw [Nat.mem_primesBelow]
      refine ⟨?_, Nat.prime_of_mem_primeFactors hp⟩
      have hple : p ≤ ⌊x⌋₊ := Nat.le_floor (hsmooth p hp)
      omega
    simpa only [hfapp] using prod_coprime_euler_factor_eq W hW0 N hsub
  rcases lt_or_ge x 2 with hx2 | hx2
  · have hfloor : ⌊x⌋₊ = 1 := by
      rw [Nat.floor_eq_iff (by linarith)]; constructor <;> [exact_mod_cast hx; exact_mod_cast hx2]
    have hWeq1 : W = 1 := by
      by_contra hWne1
      obtain ⟨p, hp⟩ : W.primeFactors.Nonempty := Nat.nonempty_primeFactors.mpr (by omega)
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
      linarith [hsmooth p hp]
    have hCHle : coprimeReciprocalSum W x ≤ 1 := by
      unfold coprimeReciprocalSum; simp [hfloor, hWeq1]
    have hrhs : (1 : ℝ) ≤ max D 1 * (Nat.totient W : ℝ) / (W : ℝ) * (Real.log x + 1) := by
      rw [hWeq1]
      simp only [Nat.totient_one, Nat.cast_one, div_one, mul_one]
      nlinarith [le_max_right D 1, hlogx_nn]
    linarith
  · have hMertens : ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ))⁻¹ ≤ D * Real.log x := by
      have hLib := hD x hx2
      rw [show ((1 : ℕ) : ℝ) = (1 : ℝ) by norm_num, pow_one] at hLib
      refine le_trans ?_ hLib
      have hp2 : ∀ p ∈ N.primesBelow, (2 : ℝ) ≤ p := fun p hp ↦ by
        exact_mod_cast (Nat.prime_of_mem_primesBelow hp).two_le
      rw [Real.exp_sum]
      refine Finset.prod_le_prod (fun p hp ↦ ?_) (fun p hp ↦ ?_) <;> have hp2 := hp2 p hp
      · have h2 : (0 : ℝ) ≤ 1 - 1 / (p : ℝ) := by
          rw [sub_nonneg, div_le_one (by linarith)]; linarith
        positivity
      · have hpne : (p : ℝ) ≠ 0 := by positivity
        have hp1 : (p : ℝ) - 1 ≠ 0 := by intro h; rw [sub_eq_zero] at h; linarith
        rw [show (1 - 1 / (p : ℝ))⁻¹ = 1 + 1 / ((p : ℝ) - 1) by field_simp; ring]
        linarith [Real.add_one_le_exp (1 / ((p : ℝ) - 1))]
    have hkey : D * Real.log x ≤ max D 1 * (Real.log x + 1) := by
      apply mul_le_mul (le_max_left D 1) (by linarith) hlogx_nn
      linarith [le_max_right D 1, hDpos.le]
    calc coprimeReciprocalSum W x ≤ ∏ p ∈ N.primesBelow, (1 - f p)⁻¹ := hdom
      _ = (Nat.totient W : ℝ) / (W : ℝ) * ∏ p ∈ N.primesBelow, (1 - 1 / (p : ℝ))⁻¹ := hfact
      _ ≤ (Nat.totient W : ℝ) / (W : ℝ) * (max D 1 * (Real.log x + 1)) :=
          mul_le_mul_of_nonneg_left (hMertens.trans hkey) hdens_nn
      _ = max D 1 * (Nat.totient W : ℝ) / (W : ℝ) * (Real.log x + 1) := by ring

/-- `sumA W R ≤ c₁ · (φ(W)/W) · log R + c₁` for `R` -smooth `W` and `2 ≤ R`, with `c₁` absolute. -/
theorem sumA_le_floor : ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ (W : ℕ) (R : ℝ), 1 ≤ W → 2 ≤ R →
      (∀ p ∈ W.primeFactors, (p : ℝ) ≤ R) →
        sumA W R ≤ c₁ * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R + c₁ := by
  obtain ⟨K, hKpos, hK⟩ := moment_sum_le
  obtain ⟨C_H, hCHpos, hCH⟩ := coprime_harmonic_le
  refine ⟨K * C_H, by positivity, ?_⟩
  intro W R hW hR hsmooth
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hW
  have hdens_le_one : (Nat.totient W : ℝ) / (W : ℝ) ≤ 1 := by
    rw [div_le_one hWpos]; exact_mod_cast Nat.totient_le W
  have hR1 : (1 : ℝ) ≤ R := by linarith
  have hCHnonneg : (0 : ℝ) ≤ coprimeReciprocalSum W R := by
    unfold coprimeReciprocalSum
    exact Finset.sum_nonneg fun m _ ↦ by positivity
  have hexpand : K * (C_H * (Nat.totient W : ℝ) / (W : ℝ) * (Real.log R + 1)) =
      K * C_H * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R +
        K * C_H * ((Nat.totient W : ℝ) / (W : ℝ)) := by
    field_simp
  have hfloor_le : K * C_H * ((Nat.totient W : ℝ) / (W : ℝ)) ≤ K * C_H := by
    simpa using mul_le_mul_of_nonneg_left hdens_le_one (by positivity : (0 : ℝ) ≤ K * C_H)
  calc sumA W R ≤ momentSum W ⌊R⌋₊ * coprimeReciprocalSum W R :=
        sumA_le_momentSum_mul_coprimeReciprocalSum W R
    _ ≤ K * coprimeReciprocalSum W R := mul_le_mul_of_nonneg_right (hK W ⌊R⌋₊) hCHnonneg
    _ ≤ K * (C_H * (Nat.totient W : ℝ) / (W : ℝ) * (Real.log R + 1)) :=
        mul_le_mul_of_nonneg_left (hCH W R hW hR1 hsmooth) hKpos.le
    _ = K * C_H * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R +
          K * C_H * ((Nat.totient W : ℝ) / (W : ℝ)) := hexpand
    _ ≤ K * C_H * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R + K * C_H := by linarith

/-- `1 ≤ (φ(W)/W) · log (N ^ (θ / 2 - δ))` for `W = primorial ⌊D₀ N⌋₊` and all large `N`, which
absorbs the additive constant of `sumA_le_floor`. -/
theorem phi_logRval_ge_one_of_large (θ δ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ N₂ : ℝ, 3 ≤ N₂ ∧ ∀ N : ℝ, N₂ ≤ N →
      (1 : ℝ) ≤ (Nat.totient (primorial ⌊D₀ N⌋₊) : ℝ) / (primorial ⌊D₀ N⌋₊ : ℝ) *
                  Real.log (N ^ (θ / 2 - δ)) := by
  obtain ⟨N₂, hN₂, hkey⟩ := primorial_D0_le_log_rpow (θ / 2 - δ) (by linarith [hδ.2])
  refine ⟨N₂, hN₂, ?_⟩
  intro N hN
  obtain ⟨-, hWle⟩ := hkey N hN
  have hWposR : (0 : ℝ) < (primorial ⌊D₀ N⌋₊ : ℝ) := by exact_mod_cast primorial_pos _
  have hphi : (1 : ℝ) ≤ (Nat.totient (primorial ⌊D₀ N⌋₊) : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (primorial_pos _)
  rw [div_mul_eq_mul_div, le_div_iff₀ hWposR, one_mul]
  linarith [mul_le_mul_of_nonneg_right hphi (hWposR.le.trans hWle)]

/-- `sumA W R ≤ c₁ · (φ(W)/W) · log R` at `W = primorial ⌊D₀ N⌋₊`, `R = N ^ (θ / 2 - δ)` and all
large `N`, with `c₁` absolute. -/
theorem sumA_le :
    ∃ c₁ : ℝ, 0 < c₁ ∧ ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
      ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → sumA (primorial ⌊D₀ N⌋₊) (N ^ (θ / 2 - δ)) ≤
          c₁ * (Nat.totient (primorial ⌊D₀ N⌋₊) : ℝ) / (primorial ⌊D₀ N⌋₊ : ℝ) *
              Real.log (N ^ (θ / 2 - δ)) := by
  obtain ⟨c₁, hc₁pos, hfloor⟩ := sumA_le_floor
  refine ⟨2 * c₁, by positivity, ?_⟩
  intro θ δ hθ hδ
  have hexp : 0 < θ / 2 - δ := by linarith [hδ.2]
  obtain ⟨N₁, hN₁3, hsmooth⟩ := primorial_D0_primeFactors_le_Rval θ δ hexp
  obtain ⟨N₂, hN₂3, hge1⟩ := phi_logRval_ge_one_of_large θ δ hδ
  refine ⟨max (max 3 N₁) (max N₂ (rexp (Real.log 2 / (θ / 2 - δ)))),
    le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro N hN
  have hR2 : (2 : ℝ) ≤ N ^ (θ / 2 - δ) := two_le_rpow_of_exp_log_two_div_le hexp
    (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have hfl := hfloor (primorial ⌊D₀ N⌋₊) (N ^ (θ / 2 - δ)) (primorial_pos _) hR2
    (hsmooth N (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN))
  have habs := hge1 N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  set W : ℕ := primorial ⌊D₀ N⌋₊
  set R : ℝ := N ^ (θ / 2 - δ)
  have hstep : c₁ ≤ c₁ * ((Nat.totient W : ℝ) / (W : ℝ) * Real.log R) := by
    simpa using mul_le_mul_of_nonneg_left habs hc₁pos.le
  have hring : 2 * c₁ * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R =
      c₁ * (Nat.totient W : ℝ) / (W : ℝ) * Real.log R +
        c₁ * ((Nat.totient W : ℝ) / (W : ℝ) * Real.log R) := by ring
  rw [hring]
  linarith

end

end MaynardOffDiagonal

end PrimeGaps
