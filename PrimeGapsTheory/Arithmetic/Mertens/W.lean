/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeDensity
public import PrimeGapsTheory.Arithmetic.Mertens.ReciprocalW

import PrimeGapsTheory.Tactic.PaperTag

/-!
# A Mertens estimate for the W-trick

A Mertens-type estimate for the coprime Möbius–totient sum with the `W`-trick modulus.

## Main results

* `mertens_W_two_sided`: A two-sided estimate for the coprime Möbius–totient sum.
* `lem_mertens_W`: The Mertens estimate for the `W`-trick modulus.
-/

@[expose] public section

open Real

open scoped Finset

open scoped BigOperators

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

open scoped PrimeGaps.sieveModulus in
/-- Reusable: eventually `exp (exp 1) ≤ (W N : ℝ)`, i.e.
`W N → ∞`. -/
theorem W_eventually_large : ∀ᶠ N in Filter.atTop, rexp (rexp 1) ≤ (W N : ℝ) := by
  set M : ℝ := rexp (rexp 1) + 1 with hM
  refine Filter.eventually_atTop.2 ⟨max (⌈rexp (rexp (rexp M))⌉₊ + 1) 3, fun N hN ↦ ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hNceil : ⌈rexp (rexp (rexp M))⌉₊ + 1 ≤ N := le_trans (le_max_left _ _) hN
  have heN : rexp 1 < (N : ℝ) := by
    have : rexp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
    exact lt_of_lt_of_le this (by exact_mod_cast hN3)
  have hbigN : rexp (rexp (rexp M)) < (N : ℝ) := by
    have h1 := Nat.le_ceil (rexp (rexp (rexp M)))
    have h2 : (⌈rexp (rexp (rexp M))⌉₊ : ℝ) + 1 ≤ (N : ℝ) := by exact_mod_cast hNceil
    linarith
  have hMlt : M < PrimeGaps.D₀ (N : ℝ) := by
    by_contra h
    push Not at h
    have := (PrimeGaps.D₀_le_self_iff heN).mp h
    exact absurd this (not_le.mpr hbigN)
  have hfloor : ⌈rexp (rexp 1)⌉₊ ≤ ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ := by
    refine Nat.le_floor ?_
    have hlt := Nat.ceil_lt_add_one (Real.exp_pos (rexp 1)).le
    rw [hM] at hMlt
    linarith
  have hWnat : ⌈rexp (rexp 1)⌉₊ ≤ W N := hfloor.trans le_primorial_self
  exact (Nat.le_ceil _).trans (by exact_mod_cast hWnat)

open scoped PrimeGaps.sieveModulus in
/-- **Weighted Mertens prime bound in terms of `loglog W`.**  There is `C_M > 0`
such that eventually in `N`, with the paper modulus `W N`,
`1 + ∑_{p|W} log p/(p-1) ≤ C_M · loglog W`.  Follows from `mertens_weighted_prime_bound`
(gives `≤ C_B(1+loglog(eW))`) plus `loglog(eW) ≤ (1+log 2)·loglog W` eventually
(since `W → ∞`, `eW ≤ W²`, `loglog W ≥ 1`), and `W` squarefree eventually. -/
theorem mertens_loglogW : ∃ C_M : ℝ, 0 < C_M ∧ ∀ᶠ N in Filter.atTop,
      1 + ∑ p ∈ (W N).primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) ≤
        C_M * Real.log (Real.log (W N : ℝ)) := by
  obtain ⟨C_B, hCB, hbound⟩ := mertens_weighted_prime_bound
  refine ⟨1 + C_B * (2 + Real.log 2), by positivity, ?_⟩
  have hWbig := W_eventually_large
  filter_upwards [hWbig] with N hW
  set Wt := W N
  have hWe : rexp 1 ≤ (Wt : ℝ) := by
    have : rexp 1 ≤ rexp (rexp 1) :=
      Real.exp_le_exp.mpr (Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 1))
    linarith
  have hWpos : (0 : ℝ) < (Wt : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hW
  have hlogW : rexp 1 ≤ Real.log (Wt : ℝ) := by
    rw [Real.le_log_iff_exp_le hWpos]; exact hW
  have hlogWpos : (0 : ℝ) < Real.log (Wt : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hlogW
  have hloglogW : (1 : ℝ) ≤ Real.log (Real.log (Wt : ℝ)) := by
    rw [Real.le_log_iff_exp_le hlogWpos]; exact hlogW
  have hsf : Squarefree Wt := PrimeGaps.W_squarefree
  have hW1 : 1 ≤ Wt := PrimeGaps.W_pos
  have hS := hbound Wt hsf hW1
  set S : ℝ := ∑ p ∈ Wt.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) with hSdef
  have heW_pos : (0 : ℝ) < rexp 1 * (Wt : ℝ) := by positivity
  have heWsq : rexp 1 * (Wt : ℝ) ≤ (Wt : ℝ) ^ 2 := by
    grw [pow_two, hWe]
  have hlog_eW_le : Real.log (rexp 1 * (Wt : ℝ)) ≤ 2 * Real.log (Wt : ℝ) := by
    have h1 : Real.log (rexp 1 * (Wt : ℝ)) ≤ Real.log ((Wt : ℝ) ^ 2) :=
      Real.log_le_log heW_pos heWsq
    have h2 : Real.log ((Wt : ℝ) ^ 2) = 2 * Real.log (Wt : ℝ) := by rw [Real.log_pow]; ring
    linarith
  have hlog_eW_pos : (0 : ℝ) < Real.log (rexp 1 * (Wt : ℝ)) := by
    rw [Real.log_mul (by positivity) (ne_of_gt hWpos), Real.log_exp]
    linarith
  have hloglog_eW : Real.log (Real.log (rexp 1 * (Wt : ℝ))) ≤
      Real.log 2 + Real.log (Real.log (Wt : ℝ)) := by
    have hmono : Real.log (Real.log (rexp 1 * (Wt : ℝ))) ≤ Real.log (2 * Real.log (Wt : ℝ)) :=
      Real.log_le_log hlog_eW_pos hlog_eW_le
    have hsplit : Real.log (2 * Real.log (Wt : ℝ)) = Real.log 2 + Real.log (Real.log (Wt : ℝ)) :=
      Real.log_mul (by norm_num) (ne_of_gt hlogWpos)
    linarith
  set L : ℝ := Real.log (Real.log (Wt : ℝ)) with hLdef
  have hstep : 1 + S ≤ 1 + C_B * (1 + (Real.log 2 + L)) := by
    have hle : C_B * (1 + Real.log (Real.log (rexp 1 * (Wt : ℝ)))) ≤
        C_B * (1 + (Real.log 2 + L)) :=
      mul_le_mul_of_nonneg_left (by linarith [hloglog_eW]) hCB.le
    linarith [hS]
  have hL1 : (1 : ℝ) ≤ L := hloglogW
  have hlog2_nonneg : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc 1 + S ≤ 1 + C_B * (1 + (Real.log 2 + L)) := hstep
    _ = 1 + C_B + C_B * Real.log 2 + C_B * L := by ring
    _ ≤ (1 + C_B * (2 + Real.log 2)) * L := by
          have hcoef : (0 : ℝ) ≤ 1 + C_B + C_B * Real.log 2 :=
            add_nonneg (add_nonneg zero_le_one hCB.le) (mul_nonneg hCB.le hlog2_nonneg)
          linarith only [mul_nonneg (sub_nonneg.mpr hL1) hcoef]

/-- `coprimeReciprocalSum W` is monotone in its real argument. -/
theorem crs_monotone (W : ℕ) : Monotone (fun Z ↦ coprimeReciprocalSum W Z) := by
  intro Z1 Z2 h
  unfold coprimeReciprocalSum
  refine Finset.sum_le_sum_of_subset_of_nonneg
    (Finset.filter_subset_filter _ (Finset.Icc_subset_Icc_right (Nat.floor_le_floor h)))
    fun i _ _ ↦ by positivity

/-- `coprimeReciprocalSum W Z ≥ 0`. -/
theorem crs_nonneg (W : ℕ) (Z : ℝ) : 0 ≤ coprimeReciprocalSum W Z := by
  unfold coprimeReciprocalSum
  exact Finset.sum_nonneg fun i _ ↦ by positivity

/-- Absolute-constant bound: `log (2√R) / R^(1/4) ≤ M₀` for all `R ≥ e`.  This lets the
polynomially-decaying tail factor be treated as a bounded quantity. -/
theorem log_sqrt_decay_bounded : ∃ M : ℝ, 0 ≤ M ∧ ∀ R : ℝ, rexp 1 ≤ R →
      Real.log (2 * √R) / (R ^ ((1 : ℝ) / 4)) ≤ M := by
  refine ⟨Real.log 2 + 4, by positivity, ?_⟩
  intro R hR
  have hRe : (1 : ℝ) ≤ R := le_trans (Real.one_le_exp (by norm_num)) hR
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (Real.exp_pos 1) hR
  have hR4pos : (0 : ℝ) < R ^ ((1 : ℝ) / 4) := Real.rpow_pos_of_pos hRpos _
  have hsqrt : √R = R ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow R
  have hlog2sqrt : Real.log (2 * √R) = Real.log 2 + (1 / 2) * Real.log R := by
    rw [hsqrt, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hRpos]
  have hlogR : Real.log R ≤ 8 * R ^ ((1 : ℝ) / 8) := by
    have := Real.log_le_rpow_div hRpos.le (show (0 : ℝ) < 1 / 8 by norm_num)
    rw [div_eq_mul_inv, show (1 / 8 : ℝ)⁻¹ = 8 by norm_num] at this
    linarith
  have hR18le : R ^ ((1 : ℝ) / 8) ≤ R ^ ((1 : ℝ) / 4) :=
    Real.rpow_le_rpow_of_exponent_le hRe (by norm_num)
  have h1leR4 : (1 : ℝ) ≤ R ^ ((1 : ℝ) / 4) := Real.one_le_rpow hRe (by norm_num)
  rw [hlog2sqrt, div_le_iff₀ hR4pos]
  have hlog2nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hhalf : (1 / 2) * Real.log R ≤ 4 * R ^ ((1 : ℝ) / 4) :=
    calc (1 / 2) * Real.log R ≤ (1 / 2) * (8 * R ^ ((1 : ℝ) / 8)) := by linarith
      _ = 4 * R ^ ((1 : ℝ) / 8) := by ring
      _ ≤ 4 * R ^ ((1 : ℝ) / 4) := by linarith [hR18le]
  calc Real.log 2 + (1 / 2) * Real.log R
      ≤ Real.log 2 * R ^ ((1 : ℝ) / 4) + 4 * R ^ ((1 : ℝ) / 4) := by
        have : Real.log 2 ≤ Real.log 2 * R ^ ((1 : ℝ) / 4) := le_mul_of_one_le_right hlog2nn h1leR4
        linarith [hhalf, this]
    _ = (Real.log 2 + 4) * R ^ ((1 : ℝ) / 4) := by ring

/-- Definitional equation for `coprimeReciprocalSum`. -/
theorem crs_eq (W : ℕ) (Z : ℝ) :
    coprimeReciprocalSum W Z = ∑ m ∈ Finset.Icc 1 ⌊Z⌋₊ with m.Coprime W, 1 / (m : ℝ) := rfl

/-- Two-sided bound for `sumA W R` about `(φ(W)/W) * log R`, the error being `(φ(W)/W)` times a
prime-factor term `∑_{p ∣ W} log p / (p - 1)` plus a tail decaying like `R ^ (-1/4)`. -/
theorem sumA_two_sided_ptwise : ∃ A B : ℝ, 0 < A ∧ 0 ≤ B ∧ ∀ (W : ℕ) (R : ℝ),
      Squarefree W → 1 ≤ W → rexp 1 ≤ R →
      √R ≥ (W : ℝ) * (#W.divisors : ℝ) / (W.totient : ℝ) →
      |PrimeGaps.MaynardOffDiagonal.sumA W R - (W.totient : ℝ) / (W : ℝ) * Real.log R| ≤
        (W.totient : ℝ) / (W : ℝ) *
            (A * (1 + ∑ p ∈ W.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1)) +
                B * (1 + Real.log R) * Real.log (2 * √R) / (R ^ ((1 : ℝ) / 4))) := by
  obtain ⟨C_A, hCA, hAssembly⟩ := coprime_harmonic_assembly
  obtain ⟨CB, hCB, hTail⟩ := gKernel_tail_bound
  obtain ⟨CC, hCC, hLogSummable, hLogtail, _⟩ := gKernel_logtail_bound
  obtain ⟨M₀, hM₀nn, hM₀⟩ := log_sqrt_decay_bounded
  have hKsummable : Summable fun n ↦ ‖gKernel n‖ := gKernel_norm_summable
  set K : ℝ := ∑' n, ‖gKernel n‖ with hKdef
  refine ⟨C_A * K + CC + C_A * CB * M₀, 2 * CB,
    by positivity, by positivity, ?_⟩
  intro W R hsf hW1 hRe hRsqrt
  set g : ℝ := (W.totient : ℝ) / (W : ℝ) with hgdef
  set L : ℝ := Real.log R with hLdef
  set S : ℝ := ∑ p ∈ W.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1) with hSdef
  set dec : ℝ := Real.log (2 * √R) / (R ^ ((1 : ℝ) / 4)) with hdecdef
  have hWpos : (0 : ℝ) < (W : ℝ) := by exact_mod_cast (by omega : 0 < W)
  have hφpos : (0 : ℝ) < (W.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega)
  have hgpos : 0 < g := by rw [hgdef]; positivity
  have hg_le_one : g ≤ 1 := by
    rw [hgdef, div_le_one hWpos]
    exact_mod_cast Nat.totient_le W
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (Real.exp_pos 1) hRe
  have hR1 : (1 : ℝ) ≤ R := le_trans (Real.one_le_exp (by norm_num)) hRe
  have hL1 : (1 : ℝ) ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hRpos]; exact hRe
  have hSnn : 0 ≤ S := by
    rw [hSdef]
    refine Finset.sum_nonneg fun p hp ↦ ?_
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
    have hplog : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by linarith)
    have hpm1 : 0 < (p : ℝ) - 1 := by linarith
    positivity
  have hsqrt1 : (1 : ℝ) ≤ √R := by
    rw [show (1 : ℝ) = √1 by simp]; exact Real.sqrt_le_sqrt hR1
  have hdecnn : 0 ≤ dec := by
    rw [hdecdef]; exact div_nonneg (Real.log_nonneg (by linarith)) (by positivity)
  have hdecM₀ : dec ≤ M₀ := by rw [hdecdef]; exact hM₀ R hRe
  rw [sumA_eq_conv W R]
  set F : Finset ℕ := {d ∈ Finset.Icc 1 ⌊R⌋₊ | d.Coprime W} with hFdef
  set h : ℕ → ℝ := fun d ↦ gKernel d * coprimeReciprocalSum W (R / d) with hhdef
  classical
  set Flo : Finset ℕ := F.filter (fun d : ℕ ↦ (d : ℝ) ≤ √R) with hFlodef
  set Fhi : Finset ℕ := F.filter (fun d : ℕ ↦ ¬ (d : ℝ) ≤ √R) with hFhidef
  have hsplit : ∑ d ∈ F, h d = (∑ d ∈ Flo, h d) + ∑ d ∈ Fhi, h d := by
    rw [hFlodef, hFhidef]
    exact (Finset.sum_filter_add_sum_filter_not F (fun d : ℕ ↦ (d : ℝ) ≤ √R) h).symm
  set Plow : ℝ := ∑ d ∈ Flo, h d with hPlowdef
  set Phi : ℝ := ∑ d ∈ Fhi, h d with hPhidef
  set f : ℕ → ℝ := fun d ↦ if d.Coprime W then gKernel d else 0 with hfdef
  have hnormabs : ∀ d, ‖gKernel d‖ = |gKernel d| := fun d ↦ Real.norm_eq_abs _
  have hTailR := hTail (√R) hsqrt1
  have hsqrtsqrt : √(√R) = R ^ ((1 : ℝ) / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hRpos)]
    norm_num
  have hTailR' : (∑' d : ℕ, if √R ≤ (d : ℝ) then |gKernel d| else 0) ≤ CB * dec := by
    have heq : CB * Real.log (2 * √R) / √(√R) = CB * dec := by
      rw [hsqrtsqrt, hdecdef]; ring
    rw [← heq]; exact hTailR
  have hIndSummable : Summable (fun d : ℕ ↦ if √R ≤ (d : ℝ) then |gKernel d| else 0) :=
    summable_ite_zero (by simpa only [hnormabs] using hKsummable)
  have hFhi_tail : ∑ d ∈ Fhi, |gKernel d| ≤ CB * dec := by
    have hrw : (∑ d ∈ Fhi, |gKernel d|) =
        ∑ d ∈ Fhi, (if √R ≤ (d : ℝ) then |gKernel d| else 0) := by
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      have hd' : √R ≤ (d : ℝ) := by
        simp only [hFhidef, hFdef, Finset.mem_filter] at hd
        push Not at hd
        exact hd.2.le
      rw [if_pos hd']
    rw [hrw]
    refine le_trans ?_ hTailR'
    exact Summable.sum_le_tsum Fhi
      (fun d _ ↦ by by_cases hc : √R ≤ (d : ℝ) <;> simp [hc])
      hIndSummable
  set σ : ℝ := ∑ d ∈ Flo, gKernel d with hσdef
  have hfFlo : ∑ d ∈ Flo, f d = σ := by
    rw [hσdef]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    have : d.Coprime W := by
      simp only [hFlodef, hFdef, Finset.mem_filter] at hd; exact hd.1.2
    simp [hfdef, this]
  have hfHasSum : HasSum f 1 := gKernel_coprime_sum_one W
  have hfSummable : Summable f := hfHasSum.summable
  have hftsum : ∑' d, f d = 1 := hfHasSum.tsum_eq
  have hgK0 : gKernel 0 = 0 := by rw [gKernel_eq_mul]; exact ArithmeticFunction.map_zero
  have hfabsSummable : Summable (fun d ↦ |f d|) := by
    apply Summable.of_nonneg_of_le (fun d ↦ abs_nonneg _) (fun d ↦ ?_)
      (by simpa only [hnormabs] using hKsummable)
    simp only [hfdef]
    by_cases hc : d.Coprime W
    · rw [if_pos hc]
    · rw [if_neg hc, abs_zero]; exact abs_nonneg _
  set G : ℕ → ℝ := fun d ↦ if √R ≤ (d : ℝ) then |gKernel d| else 0 with hGdef
  have hdom : ∀ d, ({d | d ∉ Flo}.indicator (fun d ↦ |f d|)) d ≤ G d := by
    intro d
    by_cases hmem : d ∈ Flo
    · rw [Set.indicator_of_notMem (by simpa using hmem : d ∉ {d | d ∉ Flo})]
      simp only [hGdef]
      split_ifs with hsz
      · exact abs_nonneg _
      · exact le_refl 0
    · rw [Set.indicator_of_mem (by exact hmem : d ∈ {d | d ∉ Flo})]
      simp only [hGdef]
      by_cases hc : d.Coprime W
      · simp only [hfdef, if_pos hc]
        by_cases hsz : √R ≤ (d : ℝ)
        · rw [if_pos hsz]
        · push Not at hsz
          rcases Nat.eq_zero_or_pos d with hd0 | hdpos
          · subst hd0
            rw [hgK0, abs_zero]
            split_ifs <;> simp
          · exfalso
            apply hmem
            simp only [hFlodef, hFdef, Finset.mem_filter, Finset.mem_Icc]
            refine ⟨⟨⟨hdpos, ?_⟩, hc⟩, le_of_lt hsz⟩
            have hdR : (d : ℝ) ≤ R := by
              have hsqle : √R ≤ R := Real.sqrt_le_self_iff.mpr (Or.inr hR1)
              linarith only [hsz, hsqle]
            exact Nat.le_floor hdR
      · simp only [hfdef, if_neg hc, abs_zero]
        split_ifs <;> simp
  have hσbound : |1 - σ| ≤ CB * dec := by
    have hmasseq : (∑ d ∈ Flo, f d) + ∑' d : {d // d ∉ Flo}, f d = 1 := by
      rw [Summable.sum_add_tsum_subtype_compl hfSummable Flo]; exact hftsum
    have h1σ : (1 : ℝ) - σ = ∑' d : {d // d ∉ Flo}, f d := by
      rw [← hfFlo]; linarith [hmasseq]
    rw [h1σ]
    have hstep1 : |∑' d : {d // d ∉ Flo}, f d| ≤ ∑' d : {d // d ∉ Flo}, |f d| := by
      have hfnormSummable : Summable (fun d : ℕ ↦ ‖f d‖) := by
        simpa only [Real.norm_eq_abs] using hfabsSummable
      have hsum : Summable (fun d : {d // d ∉ Flo} ↦ ‖f (d : ℕ)‖) := hfnormSummable.subtype _
      have hle := norm_tsum_le_tsum_norm hsum
      simpa only [Real.norm_eq_abs] using hle
    have hindic : (∑' d : {d // d ∉ Flo}, |f d|) =
        ∑' d, ({d | d ∉ Flo}.indicator (fun d ↦ |f d|)) d :=
      tsum_subtype {d | d ∉ Flo} (fun d ↦ |f d|)
    have hstep2 : (∑' d, ({d | d ∉ Flo}.indicator (fun d ↦ |f d|)) d) ≤ ∑' d, G d :=
      Summable.tsum_le_tsum hdom (hfabsSummable.indicator _) hIndSummable
    calc |∑' d : {d // d ∉ Flo}, f d| ≤ ∑' d : {d // d ∉ Flo}, |f d| := hstep1
      _ = ∑' d, ({d | d ∉ Flo}.indicator (fun d ↦ |f d|)) d := hindic
      _ ≤ ∑' d, G d := hstep2
      _ ≤ CB * dec := hTailR'
  rw [hsplit]
  rw [show (2 * CB * (1 + L) * Real.log (2 * √R) / (R ^ ((1 : ℝ) / 4))) =
        2 * CB * (1 + L) * dec by rw [hdecdef]; ring]
  change |Plow + Phi - g * L| ≤
      g * ((C_A * K + CC + C_A * CB * M₀) * (1 + S) + 2 * CB * (1 + L) * dec)
  set errd : ℕ → ℝ := fun d ↦ coprimeReciprocalSum W (R / d) - g * Real.log (R / d) with herrdef
  have herrbound : ∀ d ∈ Flo, |errd d| ≤ C_A * g * (1 + S) := by
    intro d hd
    simp only [hFlodef, hFdef, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨⟨hd1, _⟩, _⟩, hdle⟩ := hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hdge : (R : ℝ) / d ≥ √R := by
      rw [ge_iff_le, le_div_iff₀ hdpos]
      have hsq : √R * √R = R := Real.mul_self_sqrt (le_of_lt hRpos)
      calc √R * (d : ℝ) ≤ √R * √R :=
            mul_le_mul_of_nonneg_left hdle (Real.sqrt_nonneg R)
        _ = R := hsq
    have hxge : (R : ℝ) / d ≥ (W : ℝ) * (#W.divisors : ℝ) / (W.totient : ℝ) :=
      le_trans hRsqrt hdge
    have hA := hAssembly W hsf hW1 (R / d) hxge
    rw [herrdef]
    simp only []
    rw [crs_eq W (R / d), hgdef, hSdef]
    convert hA using 2
  have hPlow_eq : Plow = g * L * σ - g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ)) +
      (∑ d ∈ Flo, gKernel d * errd d) := by
    rw [hPlowdef, hσdef]
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    simp only [hFlodef, hFdef, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨⟨hd1, _⟩, _⟩, _⟩ := hd
    have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
    have hlogdiv : Real.log (R / d) = L - Real.log (d : ℝ) := by
      rw [Real.log_div (ne_of_gt hRpos) (ne_of_gt hdpos)]
    simp only [hhdef]
    have hrw : coprimeReciprocalSum W (R / d) = g * (L - Real.log (d : ℝ)) + errd d := by
      rw [herrdef]; simp only []; rw [hlogdiv]; ring
    rw [hrw]; ring
  have hlogterm : |∑ d ∈ Flo, gKernel d * Real.log (d : ℝ)| ≤ CC :=
    calc |∑ d ∈ Flo, gKernel d * Real.log (d : ℝ)|
        ≤ ∑ d ∈ Flo, |gKernel d * Real.log (d : ℝ)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ d ∈ Flo, |gKernel d| * Real.log (2 * (d : ℝ)) := by
          apply Finset.sum_le_sum
          intro d hd
          simp only [hFlodef, hFdef, Finset.mem_filter, Finset.mem_Icc] at hd
          obtain ⟨⟨⟨hd1, _⟩, _⟩, _⟩ := hd
          have hd1' : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd1
          have hlogdnn : 0 ≤ Real.log (d : ℝ) := Real.log_nonneg hd1'
          rw [abs_mul, abs_of_nonneg hlogdnn]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.log_le_log (by linarith only [hd1'])
          linarith only [hd1']
      _ ≤ ∑' d, |gKernel d| * Real.log (2 * (d : ℝ)) := by
          apply Summable.sum_le_tsum
          · intro d _
            rcases Nat.eq_zero_or_pos d with h0 | hp
            · simp [h0]
            · have h1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hp
              have hle2 : (1 : ℝ) ≤ 2 * (d : ℝ) := by linarith only [h1]
              exact mul_nonneg (abs_nonneg _) (Real.log_nonneg hle2)
          · simpa only [hnormabs] using hLogSummable
      _ ≤ CC := hLogtail
  have hepsterm : |∑ d ∈ Flo, gKernel d * errd d| ≤ C_A * g * (1 + S) * K :=
    calc |∑ d ∈ Flo, gKernel d * errd d|
        ≤ ∑ d ∈ Flo, |gKernel d * errd d| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Flo, |gKernel d| * |errd d| :=
          Finset.sum_congr rfl fun d _ ↦ abs_mul _ _
      _ ≤ ∑ d ∈ Flo, |gKernel d| * (C_A * g * (1 + S)) :=
          Finset.sum_le_sum fun d hd ↦
            mul_le_mul_of_nonneg_left (herrbound d hd) (abs_nonneg _)
      _ = (∑ d ∈ Flo, |gKernel d|) * (C_A * g * (1 + S)) := by rw [Finset.sum_mul]
      _ ≤ K * (C_A * g * (1 + S)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [hKdef]
          calc ∑ d ∈ Flo, |gKernel d|
              ≤ ∑' d, |gKernel d| := Summable.sum_le_tsum _ (fun d _ ↦ abs_nonneg _)
                (by simpa only [hnormabs] using hKsummable)
            _ = ∑' d, ‖gKernel d‖ := by simp only [hnormabs]
      _ = C_A * g * (1 + S) * K := by ring
  have hPlow_bound : |Plow - g * L| ≤ g * L * (CB * dec) + g * CC + C_A * g * (1 + S) * K := by
    have heq : Plow - g * L = - (g * L * (1 - σ)) - g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ)) +
          (∑ d ∈ Flo, gKernel d * errd d) := by
      rw [hPlow_eq]; ring
    rw [heq]
    calc |- (g * L * (1 - σ)) - g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ)) +
            (∑ d ∈ Flo, gKernel d * errd d)| ≤
        |- (g * L * (1 - σ)) - g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ))| +
            |∑ d ∈ Flo, gKernel d * errd d| := abs_add_le _ _
      _ ≤ (|- (g * L * (1 - σ))| + |g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ))|) +
            |∑ d ∈ Flo, gKernel d * errd d| := by
          have hsub : |- (g * L * (1 - σ)) - g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ))| ≤
              |- (g * L * (1 - σ))| + |g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ))| :=
            abs_sub _ _
          linarith [hsub]
      _ ≤ g * L * (CB * dec) + g * CC + C_A * g * (1 + S) * K := by
          have hb1 : |- (g * L * (1 - σ))| ≤ g * L * (CB * dec) := by
            rw [abs_neg, abs_mul, abs_mul, abs_of_nonneg (le_of_lt hgpos),
                abs_of_nonneg (le_trans zero_le_one hL1)]
            exact mul_le_mul_of_nonneg_left hσbound (by positivity)
          have hb2 : |g * (∑ d ∈ Flo, gKernel d * Real.log (d : ℝ))| ≤ g * CC := by
            rw [abs_mul, abs_of_nonneg (le_of_lt hgpos)]
            exact mul_le_mul_of_nonneg_left hlogterm (le_of_lt hgpos)
          linarith [hb1, hb2, hepsterm]
  set bnd : ℝ := g * (L / 2) + C_A * g * (1 + S) with hbnddef
  have hbnd_nn : 0 ≤ bnd := by
    rw [hbnddef]; positivity
  have hcrs_sqrt : coprimeReciprocalSum W (√R) ≤ bnd := by
    have hxge : √R ≥ (W : ℝ) * (#W.divisors : ℝ) / (W.totient : ℝ) := hRsqrt
    have hassemb := hAssembly W hsf hW1 (√R) hxge
    have hlogsqrt : Real.log (√R) = L / 2 := by
      rw [Real.log_sqrt (le_of_lt hRpos), hLdef]
    have hub : coprimeReciprocalSum W (√R) - g * Real.log (√R) ≤
        C_A * g * (1 + S) := le_trans (le_abs_self _) hassemb
    rw [hlogsqrt] at hub
    rw [hbnddef]; linarith [hub]
  have hPhi_bound : |Phi| ≤ bnd * (CB * dec) :=
    calc |Phi| ≤ ∑ d ∈ Fhi, |h d| := by rw [hPhidef]; exact Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ Fhi, |gKernel d| * coprimeReciprocalSum W (R / d) :=
          Finset.sum_congr rfl fun d _ ↦ by
            rw [hhdef, abs_mul, abs_of_nonneg (crs_nonneg W (R / d))]
      _ ≤ ∑ d ∈ Fhi, |gKernel d| * bnd := by
          refine Finset.sum_le_sum fun d hd ↦ ?_
          refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
          simp only [hFhidef, hFdef, Finset.mem_filter, Finset.mem_Icc] at hd
          obtain ⟨⟨⟨hd1, _⟩, _⟩, hdgt⟩ := hd
          push Not at hdgt
          have hdpos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
          have hle : (R : ℝ) / d ≤ √R := by
            rw [div_le_iff₀ hdpos]
            calc R = √R * √R := (Real.mul_self_sqrt hRpos.le).symm
              _ ≤ √R * (d : ℝ) := mul_le_mul_of_nonneg_left hdgt.le (Real.sqrt_nonneg R)
          exact (crs_monotone W hle).trans hcrs_sqrt
      _ = (∑ d ∈ Fhi, |gKernel d|) * bnd := by rw [Finset.sum_mul]
      _ ≤ (CB * dec) * bnd := mul_le_mul_of_nonneg_right hFhi_tail hbnd_nn
      _ = bnd * (CB * dec) := by ring
  have htri : |Plow + Phi - g * L| ≤ |Plow - g * L| + |Phi| := by
    rw [show Plow + Phi - g * L = (Plow - g * L) + Phi by ring]; exact abs_add_le _ _
  refine htri.trans ((add_le_add hPlow_bound hPhi_bound).trans ?_)
  rw [hbnddef]
  have hdecM₀' : C_A * g * (1 + S) * (CB * dec) ≤ C_A * g * (1 + S) * (CB * M₀) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecM₀ hCB.le) (by positivity)
  have e1 : (0 : ℝ) ≤ g * CC * S := mul_nonneg (mul_nonneg hgpos.le hCC.le) hSnn
  have e2 : (0 : ℝ) ≤ g * CB * L * dec :=
    mul_nonneg (mul_nonneg (mul_nonneg hgpos.le hCB.le) (zero_le_one.trans hL1)) hdecnn
  have e3 : (0 : ℝ) ≤ g * CB * dec := mul_nonneg (mul_nonneg hgpos.le hCB.le) hdecnn
  linarith only [hdecM₀', e1, e2, e3]

/-- For a natural `N ≥ 3` one has `e ≤ N`, since `e < 3`. -/
private lemma exp_one_le_of_three_le {N : ℕ} (hN : 3 ≤ N) : rexp 1 ≤ (N : ℝ) := by
  have h3 : rexp 1 < 3 := by have := Real.exp_one_lt_d9; linarith
  exact le_of_lt (lt_of_lt_of_le h3 (by exact_mod_cast hN))

/-- If `e ≤ x` then `1 ≤ log x`. -/
private lemma one_le_log_of_exp_one_le {x : ℝ} (hx : rexp 1 ≤ x) : 1 ≤ Real.log x :=
  (Real.le_log_iff_exp_le ((Real.exp_pos 1).trans_le hx)).mpr hx

/-- A product of two affine functions of `L`, scaled by `B ≥ 0`, is at most `L⁴` as soon as
`L ≥ 1` dominates the constant `(B + 1)(1 + c)(log 2 + c)`. -/
private lemma affine_mul_affine_le_pow_four {B c L : ℝ} (hB : 0 ≤ B) (hc : 0 < c) (hL1 : 1 ≤ L)
    (hLN : (B + 1) * (1 + c) * (Real.log 2 + c) ≤ L) :
    B * (1 + c * L) * (Real.log 2 + c / 2 * L) ≤ L ^ (4 : ℕ) := by
  have hlog2_nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hf1 : 1 + c * L ≤ (1 + c) * L := by linarith only [hL1]
  have hf2 : Real.log 2 + c / 2 * L ≤ (Real.log 2 + c) * L := by
    linarith only [mul_nonneg hlog2_nn (sub_nonneg.mpr hL1),
      mul_nonneg hc.le (zero_le_one.trans hL1)]
  have hBL : B * ((1 + c) * L) * ((Real.log 2 + c) * L) =
      (B * (1 + c) * (Real.log 2 + c)) * L ^ 2 := by ring
  have hprod : B * (1 + c * L) * (Real.log 2 + c / 2 * L) ≤
      (B * (1 + c) * (Real.log 2 + c)) * L ^ 2 := by
    rw [← hBL]
    have hnn1 : (0 : ℝ) ≤ 1 + c * L := by positivity
    have hnn2 : (0 : ℝ) ≤ Real.log 2 + c / 2 * L := by positivity
    have hnnf1 : (0 : ℝ) ≤ (1 + c) * L := by positivity
    calc B * (1 + c * L) * (Real.log 2 + c / 2 * L)
        ≤ B * ((1 + c) * L) * (Real.log 2 + c / 2 * L) := by
          apply mul_le_mul_of_nonneg_right _ hnn2
          exact mul_le_mul_of_nonneg_left hf1 hB
      _ ≤ B * ((1 + c) * L) * ((Real.log 2 + c) * L) := by
          apply mul_le_mul_of_nonneg_left hf2
          positivity
  have hK : B * (1 + c) * (Real.log 2 + c) ≤ L := by
    have h1c : (0 : ℝ) ≤ 1 + c := by linarith only [hc.le]
    have hlc : (0 : ℝ) ≤ Real.log 2 + c := by linarith only [hlog2_nn, hc.le]
    have : B * (1 + c) * (Real.log 2 + c) ≤ (B + 1) * (1 + c) * (Real.log 2 + c) := by
      linarith only [mul_nonneg h1c hlc]
    linarith only [hLN, this]
  have hL2nn : (0 : ℝ) ≤ L ^ 2 := by positivity
  calc B * (1 + c * L) * (Real.log 2 + c / 2 * L)
      ≤ (B * (1 + c) * (Real.log 2 + c)) * L ^ 2 := hprod
    _ ≤ L * L ^ 2 := mul_le_mul_of_nonneg_right hK hL2nn
    _ = L ^ 3 := by ring
    _ ≤ L ^ (4 : ℕ) := pow_le_pow_right₀ hL1 (by norm_num)

/-- For `V ≥ 1` one has `V·τ(V)/φ(V) ≤ V²`, since `τ(V) ≤ V` and `φ(V) ≥ 1`. -/
private lemma mul_card_divisors_div_totient_le_sq {V : ℕ} (hV : 1 ≤ V) :
    (V : ℝ) * #V.divisors / V.totient ≤ (V : ℝ) * V := by
  have hVpos : (0 : ℝ) < (V : ℝ) := by exact_mod_cast (by omega : 0 < V)
  have hτ : (#V.divisors : ℝ) ≤ (V : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self V
  have hφ1 : (1 : ℝ) ≤ (V.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < V)
  have hφpos : (0 : ℝ) < (V.totient : ℝ) := by linarith
  rw [div_le_iff₀ hφpos]
  calc (V : ℝ) * #V.divisors ≤ (V : ℝ) * V := mul_le_mul_of_nonneg_left hτ hVpos.le
    _ = (V : ℝ) * V * 1 := by ring
    _ ≤ (V : ℝ) * V * V.totient := mul_le_mul_of_nonneg_left hφ1 (mul_nonneg hVpos.le hVpos.le)

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **Eventual size preliminaries.**  Eventually in `N`, with the paper modulus `W N`,
the paper truncation `R`: `W` is squarefree, `1 ≤ W`, `e ≤ R`, `√R ≥ W·τ(W)/φ(W)`,
`1 ≤ loglog W`, `1 ≤ φW/W`... and the polynomially-decaying tail factor is dominated:
`B·(1+log R)·log(2√R)/R^{1/4} ≤ loglog W` (uses `√R = N^c` and `W ≤ (loglog N)²`,
hence `φW/W ≥ 1/W ≥ 1/(loglog N)²`, so any poly-in-N decay beats it).  Bundled to feed
`sumA_two_sided_ptwise` and `mertens_loglogW`. -/
theorem size_prelims (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) (B : ℝ) (hB : 0 ≤ B) :
    ∀ᶠ N in Filter.atTop, Squarefree (W N) ∧ 1 ≤ W N ∧ rexp 1 ≤ R ∧
      √R ≥ (W N : ℝ) * (#(W N).divisors : ℝ) / ((W N).totient : ℝ) ∧
      1 ≤ Real.log (Real.log (W N : ℝ)) ∧
      B * (1 + Real.log R) * Real.log (2 * √R) / (R ^ ((1 : ℝ) / 4)) ≤
        Real.log (Real.log (W N : ℝ)) := by
  obtain ⟨hδ, hδθ2, hθ1⟩ := hδθ
  set c : ℝ := θ / 2 - δ with hc_def
  have hc : 0 < c := by simp only [hc_def]; linarith
  have hR_eq : ∀ N : ℕ, R = (N : ℝ) ^ c := fun _ ↦ rfl
  have hNe : ∀ᶠ N : ℕ in Filter.atTop, rexp 1 ≤ (N : ℝ) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with N hN
    exact exp_one_le_of_three_le hN
  have hWinf := W_eventually_large
  have hWsize := PrimeGaps.lem_W_size
  have hgrow4 : ∀ᶠ N : ℕ in Filter.atTop, (Real.log (N : ℝ)) ^ (4 : ℕ) ≤ (N : ℝ) ^ (c / 2) :=
    tendsto_natCast_atTop_atTop.eventually (eventually_log_pow_le_rpow 4 (by linarith))
  have hRbig : ∀ᶠ N : ℕ in Filter.atTop, rexp 1 ≤ (N : ℝ) ^ c := by
    have h : Filter.Tendsto (fun N : ℕ ↦ (N : ℝ) ^ c) Filter.atTop Filter.atTop :=
      (tendsto_rpow_atTop hc).comp tendsto_natCast_atTop_atTop
    exact h.eventually_ge_atTop (rexp 1)
  have htail0 : ∀ᶠ N : ℕ in Filter.atTop,
      B * (1 + Real.log ((N : ℝ) ^ c)) * Real.log (2 * √((N : ℝ) ^ c)) /
          (((N : ℝ) ^ c) ^ ((1 : ℝ) / 4)) ≤ 1 := by
    have hgrow4' : ∀ᶠ N : ℕ in Filter.atTop, (Real.log (N : ℝ)) ^ (4 : ℕ) ≤ (N : ℝ) ^ (c / 4) :=
      tendsto_natCast_atTop_atTop.eventually (eventually_log_pow_le_rpow 4 (by linarith))
    have hLbig : ∀ᶠ N : ℕ in Filter.atTop,
        (B + 1) * (1 + c) * (Real.log 2 + c) ≤ Real.log (N : ℝ) := by
      have hlog : Filter.Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) Filter.atTop Filter.atTop :=
        Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
      exact hlog.eventually_ge_atTop _
    filter_upwards [hgrow4', hLbig, Filter.eventually_ge_atTop 3] with N hden hLN hN3
    have hNe : rexp 1 ≤ (N : ℝ) := exp_one_le_of_three_le hN3
    have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
    have hNcpos : (0 : ℝ) < (N : ℝ) ^ c := by positivity
    have hL1 : (1 : ℝ) ≤ Real.log (N : ℝ) := one_le_log_of_exp_one_le hNe
    set L : ℝ := Real.log (N : ℝ) with hLdef
    have hlogNc : Real.log ((N : ℝ) ^ c) = c * L := by
      rw [hLdef, Real.log_rpow hNpos]
    have hsqrt : √((N : ℝ) ^ c) = (N : ℝ) ^ (c / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (le_of_lt hNpos)]; ring_nf
    have hden_eq : ((N : ℝ) ^ c) ^ ((1 : ℝ) / 4) = (N : ℝ) ^ (c / 4) := by
      rw [← Real.rpow_mul (le_of_lt hNpos)]; ring_nf
    have hlog2sqrt : Real.log (2 * √((N : ℝ) ^ c)) = Real.log 2 + (c / 2) * L := by
      rw [hsqrt, Real.log_mul (by norm_num) (by positivity), Real.log_rpow hNpos]
    rw [hlogNc, hlog2sqrt, hden_eq]
    have hdenpos : (0 : ℝ) < (N : ℝ) ^ (c / 4) := by positivity
    have hlog2_le1 : Real.log 2 ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith
    have hlog2_nn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    rw [div_le_one hdenpos]
    have hnum_le : B * (1 + c * L) * (Real.log 2 + c / 2 * L) ≤ L ^ (4 : ℕ) :=
      affine_mul_affine_le_pow_four hB hc hL1 hLN
    calc B * (1 + c * L) * (Real.log 2 + c / 2 * L) ≤ L ^ (4 : ℕ) := hnum_le
      _ ≤ (N : ℝ) ^ (c / 4) := hden
  filter_upwards [hNe, hWinf, hWsize, hgrow4, hRbig, htail0,
      Filter.eventually_ge_atTop 3] with N hNe hWinf hWsize hgrow4 hRbig htail0 hN3
  set Wt := W N
  have hsf : Squarefree Wt := PrimeGaps.W_squarefree
  have hW1 : 1 ≤ Wt := PrimeGaps.W_pos
  have hWpos : (0 : ℝ) < (Wt : ℝ) := by exact_mod_cast (by omega : 0 < Wt)
  have hWe : rexp 1 ≤ (Wt : ℝ) := by
    have : rexp 1 ≤ rexp (rexp 1) :=
      Real.exp_le_exp.mpr (Real.one_le_exp (by norm_num))
    linarith [hWinf]
  have hlogW : rexp 1 ≤ Real.log (Wt : ℝ) := by
    rw [Real.le_log_iff_exp_le hWpos]; exact hWinf
  have hlogWpos : (0 : ℝ) < Real.log (Wt : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hlogW
  have hll1 : (1 : ℝ) ≤ Real.log (Real.log (Wt : ℝ)) := by
    rw [Real.le_log_iff_exp_le hlogWpos]; exact hlogW
  have hconj4 : √R ≥ (Wt : ℝ) * #Wt.divisors / Wt.totient := by
    rw [hR_eq]
    have hNpos : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
    have hsqrt : √((N : ℝ) ^ c) = (N : ℝ) ^ (c / 2) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hNpos]; ring_nf
    rw [hsqrt, ge_iff_le]
    have hRHS_le : (Wt : ℝ) * #Wt.divisors / Wt.totient ≤ (Wt : ℝ) * Wt :=
      mul_card_divisors_div_totient_le_sq hW1
    have hlogN1 : (1 : ℝ) ≤ Real.log (N : ℝ) := one_le_log_of_exp_one_le hNe
    have hloglogNnn : (0 : ℝ) ≤ Real.log (Real.log (N : ℝ)) := Real.log_nonneg hlogN1
    have hWsq : (Wt : ℝ) * Wt ≤ (Real.log (Real.log (N : ℝ))) ^ 4 := by
      have := mul_le_mul hWsize hWsize hWpos.le (by positivity)
      calc (Wt : ℝ) * Wt
          ≤ (Real.log (Real.log (N : ℝ)) ^ 2) * (Real.log (Real.log (N : ℝ)) ^ 2) := this
        _ = (Real.log (Real.log (N : ℝ))) ^ 4 := by ring
    have hloglog_le : Real.log (Real.log (N : ℝ)) ≤ Real.log (N : ℝ) :=
      (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    have hll4 : (Real.log (Real.log (N : ℝ))) ^ 4 ≤ (Real.log (N : ℝ)) ^ 4 := by gcongr
    calc (Wt : ℝ) * #Wt.divisors / Wt.totient ≤ (Wt : ℝ) * Wt := hRHS_le
      _ ≤ (Real.log (Real.log (N : ℝ))) ^ 4 := hWsq
      _ ≤ (Real.log (N : ℝ)) ^ 4 := hll4
      _ ≤ (N : ℝ) ^ (c / 2) := hgrow4
  have hconj6 : B * (1 + Real.log R) * Real.log (2 * √R) /
      (R ^ ((1 : ℝ) / 4)) ≤ Real.log (Real.log (Wt : ℝ)) := by
    rw [hR_eq]; exact htail0.trans hll1
  exact ⟨hsf, hW1, by rw [hR_eq]; exact hRbig, hconj4, hll1, hconj6⟩

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Two-sided Mertens estimate for `PrimeGaps.MaynardOffDiagonal.sumA`, eventual in `N`:
there is `C > 0` such
that, with the paper modulus `W N` and the paper truncation `R`, eventually
`|PrimeGaps.MaynardOffDiagonal.sumA W R − (φW/W)·log R| ≤ C·(φW/W)·log log W`.
This combines the pointwise core
`sumA_two_sided_ptwise` with the eventual size bounds `size_prelims` and the
`log log W` prime bound `mertens_loglogW`. -/
theorem sumA_two_sided (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in Filter.atTop,
      |PrimeGaps.MaynardOffDiagonal.sumA (W N) R - ((W N).totient : ℝ) / (W N : ℝ) * Real.log R| ≤
        C * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (Real.log (W N : ℝ)) := by
  obtain ⟨A, B, hA, hB, hptwise⟩ := sumA_two_sided_ptwise
  obtain ⟨C_M, hCM, hMloglog⟩ := mertens_loglogW
  refine ⟨A * C_M + 1, by positivity, ?_⟩
  filter_upwards [size_prelims δ θ hδθ B hB, hMloglog] with N hsize hMl
  obtain ⟨hsf, hW1, hRe, hRsqrt, hll1, htail⟩ := hsize
  set Wt := W N
  set Rt := R
  set g : ℝ := (Wt.totient : ℝ) / (Wt : ℝ)
  have hgpos : 0 < g :=
    div_pos (by exact_mod_cast Nat.totient_pos.mpr (by omega))
      (by exact_mod_cast (by omega : 0 < Wt))
  set S : ℝ := ∑ p ∈ Wt.primeFactors, Real.log (p : ℝ) / ((p : ℝ) - 1)
  have hpt := hptwise Wt Rt hsf hW1 hRe hRsqrt
  calc |PrimeGaps.MaynardOffDiagonal.sumA Wt Rt - g * Real.log Rt| ≤ g * (A * (1 + S) +
          B * (1 + Real.log Rt) * Real.log (2 * √Rt) / (Rt ^ ((1 : ℝ) / 4))) := hpt
    _ ≤ g * (A * (C_M * Real.log (Real.log (Wt : ℝ))) +
          Real.log (Real.log (Wt : ℝ))) := by
          refine mul_le_mul_of_nonneg_left ?_ hgpos.le
          have h1 : A * (1 + S) ≤ A * (C_M * Real.log (Real.log (Wt : ℝ))) :=
            mul_le_mul_of_nonneg_left hMl hA.le
          have h2 : B * (1 + Real.log Rt) * Real.log (2 * √Rt) /
              (Rt ^ ((1 : ℝ) / 4)) ≤ Real.log (Real.log (Wt : ℝ)) := htail
          linarith
    _ = (A * C_M + 1) * g * Real.log (Real.log (Wt : ℝ)) := by ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- A two-sided Mertens estimate for `MaynardOffDiagonal.sumA`. -/
theorem mertens_W_two_sided (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in Filter.atTop,
      |MaynardOffDiagonal.sumA (W N) R - ((W N).totient : ℝ) / (W N : ℝ) * Real.log R| ≤
        C * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (Real.log (W N : ℝ)) :=
  sumA_two_sided δ θ hδθ

end PrimeGaps

namespace PrimeGaps

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **Mertens-type estimate `lem_mertens_W`.** For the paper truncation `R`
and modulus `W N`, there is `C > 0` such that eventually in `N` the coprime `μ²/φ`
sum satisfies
`|∑_{u ≤ ⌊R⌋₊, (u,W)=1} μ(u)²/φ(u) − (φW/W)·log R| ≤ C·(φW/W)·log log W`.
This is the headline result of the file; it follows from `PrimeGaps.mertens_W_two_sided`
after rewriting the sum as `MaynardOffDiagonal.sumA`. -/
@[pg_tag "bg246" "lem_mertens_W"]
theorem lem_mertens_W (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in Filter.atTop,
      |(∑ u ∈ {u ∈ (Finset.Icc 1 ⌊R⌋₊) | Nat.Coprime u (W N)},
            ((μ u : ℝ) ^ 2 / (Nat.totient u : ℝ))) -
          ((W N).totient : ℝ) / (W N : ℝ) * Real.log R| ≤
        C * (((W N).totient : ℝ) / (W N : ℝ)) *
            Real.log (Real.log (W N : ℝ)) := by
  obtain ⟨C, hC, hev⟩ := PrimeGaps.mertens_W_two_sided δ θ hδθ
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev] with N hN
  rwa [← sumA_eq_mobiusTotientSum (W N) R]

end PrimeGaps
