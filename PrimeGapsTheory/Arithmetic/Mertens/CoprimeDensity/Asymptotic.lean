/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeDensity.DyadicTail

import PrimeGapsTheory.Tactic.PaperTag

/-!
# The coprime-density asymptotic

The asymptotic for the coprime-restricted convolution and for `sumA`.

## Main results

* `exists_abs_sumA_sub_le`
-/

@[expose] public section

open PrimeGaps.MertensShared Finset ArithmeticFunction

namespace PrimeGaps

/-- **KEY inequality `ellV m ≤ τ(m)`.**  For squarefree `m`,
`ellV m = ∑_{p∣m} log p/(p−1) ≤ #primeFactors ≤ 2^{#primeFactors} = #divisors`,
using `log p ≤ p−1` (so each summand `≤ 1`).  This makes ONE log suffice in `conv_asymptotic`. -/
lemma ellV_le_tau (m : ℕ) (hsq : Squarefree m) : ellV m ≤ (#m.divisors : ℝ) := by
  classical
  by_cases hm0 : m = 0
  · subst hm0; simp [ellV]
  have hsub : m.primeFactors ⊆ m.divisors := fun p hp ↦
    Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, hm0⟩
  unfold ellV
  calc (∑ p ∈ m.primeFactors, Real.log ↑p / (↑p - 1)) ≤ (∑ _ ∈ m.primeFactors, (1 : ℝ)) := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
        rw [div_le_one (by linarith)]
        linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < (p : ℝ) by linarith)]
    _ = (#m.primeFactors : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ (#m.divisors : ℝ) := by exact_mod_cast Finset.card_le_card hsub

/-- Restricting a summable family of reals to the indices satisfying a predicate, by
setting all other terms to `0`, leaves it summable. -/
lemma summable_ite_zero {f : ℕ → ℝ} (hf : Summable f) {P : ℕ → Prop} [DecidablePred P] :
    Summable fun d : ℕ ↦ if P d then f d else 0 :=
  (hf.indicator {d : ℕ | P d}).congr fun d ↦ by simp [Set.indicator_apply]

/-- The coprimality-restricted kernel-times-log term `g(d) · log d` is dominated in norm by
`|g(d)| · log (2d)`, the summand of the convergent bound in `gKernel_logtail_bound`. -/
private lemma norm_ite_coprime_gKernel_mul_log_le (m d : ℕ) :
    ‖(if Nat.Coprime d m then gKernel d * Real.log (d : ℝ) else 0)‖ ≤
      |gKernel d| * Real.log (2 * (d : ℝ)) := by
  rcases Nat.eq_zero_or_pos d with hd0 | hdpos
  · subst hd0; simp
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
  have hloglog : |Real.log (d : ℝ)| ≤ Real.log (2 * (d : ℝ)) := by
    rw [abs_of_nonneg (Real.log_nonneg hd1)]
    exact Real.log_le_log (by linarith only [hd1]) (by linarith only [hd1])
  by_cases hcop : Nat.Coprime d m
  · rw [if_pos hcop, Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left hloglog (abs_nonneg _)
  · rw [if_neg hcop, norm_zero]
    exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith only [hd1]))

/-- For `m ≥ 1` the density `φ(m)/m` is positive. -/
private lemma totient_div_self_pos {m : ℕ} (hm : 1 ≤ m) : 0 < (Nat.totient m : ℝ) / m :=
  div_pos (by exact_mod_cast Nat.totient_pos.mpr (by omega))
    (by exact_mod_cast (by omega : 0 < m))

/-- For `m ≥ 1` the density `φ(m)/m` is at most `1`. -/
private lemma totient_div_self_le_one {m : ℕ} (hm : 1 ≤ m) : (Nat.totient m : ℝ) / m ≤ 1 := by
  rw [div_le_one (by exact_mod_cast (by omega : 0 < m))]
  exact_mod_cast Nat.totient_le m

/-- For `m ≥ 1` the divisor count `τ(m)` is at least `1`. -/
private lemma one_le_cast_card_divisors {m : ℕ} (hm : 1 ≤ m) : (1 : ℝ) ≤ (#m.divisors : ℝ) := by
  have hpos : 0 < #m.divisors :=
    Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  exact_mod_cast hpos

/-- A summable family supported on the integers coprime to `m` and vanishing at `0` splits as
its partial sum over `1 ≤ d ≤ ⌊x⌋` plus its tail over `d > x`. -/
private lemma tsum_eq_sum_coprime_add_tsum_gt (m : ℕ) (x : ℝ) (hx : 0 ≤ x) (h : ℕ → ℝ)
    (hsum : Summable h) (hsupp : ∀ d, ¬ Nat.Coprime d m → h d = 0) (hzero : h 0 = 0) :
    (∑' (d : ℕ), h d) = (∑ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m), h d) +
        (∑' (d : ℕ), if x < (d : ℝ) then h d else 0) := by
  have hxfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hsum1 : Summable (fun d : ℕ ↦ if (d : ℝ) ≤ x then h d else 0) := summable_ite_zero hsum
  have hsum2 : Summable (fun d : ℕ ↦ if x < (d : ℝ) then h d else 0) := summable_ite_zero hsum
  have hpt : ∀ d : ℕ,
      h d = (if (d : ℝ) ≤ x then h d else 0) + (if x < (d : ℝ) then h d else 0) := fun d ↦ by
    rcases le_or_gt (d : ℝ) x with hd | hd
    · rw [if_pos hd, if_neg (not_lt.2 hd), add_zero]
    · rw [if_neg (not_le.2 hd), if_pos hd, zero_add]
  rw [tsum_congr hpt, hsum1.tsum_add hsum2]
  congr 1
  rw [tsum_eq_sum (s := (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m)) ?_]
  · refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_filter, Finset.mem_Icc] at hd
    exact if_pos ((by exact_mod_cast hd.1.2 : (d : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans hxfloor_le)
  · intro d hdD
    by_cases hle : (d : ℝ) ≤ x
    · rw [if_pos hle]
      by_cases hcop : Nat.Coprime d m
      · rcases Nat.eq_zero_or_pos d with hd0 | hdpos
        · subst hd0; exact hzero
        · exact (hdD (Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hdpos, Nat.le_floor (by exact_mod_cast hle)⟩, hcop⟩)).elim
      · exact hsupp d hcop
    · rw [if_neg hle]

/-- **Hyperbola decomposition.**  The difference between the convolution sum
`∑_{d ≤ x, (d,m)=1} g(d) · ∑_{k ≤ x/d, (k,m)=1} 1/k` and its main term
`φ(m)/m · (log x + ℓ(m))` is the Euler–Mascheroni term `φ(m)/m · (γ − ∑_{(d,m)=1} g(d) log d)`,
minus the tail correction over `d > x`, plus the remainder assembled from the pointwise error
of the inner coprime harmonic sum. -/
private lemma conv_sub_main_eq (m : ℕ) (x : ℝ) (hxpos : 0 < x) :
    (∑ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m),
          gKernel d * coprimeReciprocalSum m (x / d)) -
        (Nat.totient m : ℝ) / m * (Real.log x + ellV m) =
      (Nat.totient m : ℝ) / m * (Real.eulerMascheroniConstant -
          ∑' d : ℕ, if Nat.Coprime d m then gKernel d * Real.log d else 0) -
        (Nat.totient m : ℝ) / m * (∑' d : ℕ, if ((x < (d : ℝ)) ∧ Nat.Coprime d m) then
          gKernel d * (Real.log (x / d) + Real.eulerMascheroniConstant + ellV m) else 0) +
        ∑ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m),
          gKernel d * (coprimeReciprocalSum m (x / d) - (Nat.totient m : ℝ) / m *
            (Real.log (x / d) + Real.eulerMascheroniConstant + ellV m)) := by
  classical
  obtain ⟨-, -, hCCsummable, -, -⟩ := gKernel_logtail_bound
  set L : ℝ := (Nat.totient m : ℝ) / m with hLdef
  set γ : ℝ := Real.eulerMascheroniConstant
  set D : Finset ℕ := (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m) with hDdef
  set conv : ℝ := ∑ d ∈ D, gKernel d * coprimeReciprocalSum m (x / d) with hconvdef
  set R : ℝ := ∑ d ∈ D,
      gKernel d * (coprimeReciprocalSum m (x / d) - L * (Real.log (x / d) + γ + ellV m))
    with hRdef
  set E : ℝ := ∑' d : ℕ, if ((x < (d : ℝ)) ∧ Nat.Coprime d m) then
        gKernel d * (Real.log (x / d) + γ + ellV m) else 0
    with hEdef
  set P : ℕ → ℝ := fun d ↦ Real.log (x / d) + γ + ellV m with hPdef
  have hF1 : HasSum (fun d : ℕ ↦ if Nat.Coprime d m then gKernel d else 0) 1 :=
    gKernel_coprime_sum_one m
  have hCgL : Summable (fun d : ℕ ↦ if Nat.Coprime d m then gKernel d * Real.log (d : ℝ) else 0) :=
    Summable.of_norm_bounded (g := fun d : ℕ ↦ |gKernel d| * Real.log (2 * (d : ℝ)))
      hCCsummable (norm_ite_coprime_gKernel_mul_log_le m)
  -- Split a coprimality-restricted summable family into its part over `D` and its tail.
  have hsplit : ∀ f : ℕ → ℝ, Summable (fun d : ℕ ↦ if Nat.Coprime d m then f d else 0) →
      (if Nat.Coprime 0 m then f 0 else 0) = 0 →
      (∑ d ∈ D, f d) = (∑' d : ℕ, if Nat.Coprime d m then f d else 0) -
        ∑' d : ℕ, if x < (d : ℝ) then (if Nat.Coprime d m then f d else 0) else 0 := by
    intro f hsum hzero
    have hkey : (∑' d : ℕ, if Nat.Coprime d m then f d else 0) =
        (∑ d ∈ D, if Nat.Coprime d m then f d else 0) +
          ∑' d : ℕ, if x < (d : ℝ) then (if Nat.Coprime d m then f d else 0) else 0 := by
      rw [hDdef]
      exact tsum_eq_sum_coprime_add_tsum_gt m x hxpos.le _ hsum (fun d hd ↦ if_neg hd) hzero
    have hDeq : (∑ d ∈ D, if Nat.Coprime d m then f d else 0) = ∑ d ∈ D, f d := by
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      rw [hDdef, Finset.mem_filter] at hd
      exact if_pos hd.2
    rw [hDeq] at hkey
    linarith only [hkey]
  have h3a : (∑ d ∈ D, gKernel d) =
      1 - ∑' d : ℕ, if x < (d : ℝ) then (if Nat.Coprime d m then gKernel d else 0) else 0 := by
    have h := hsplit gKernel hF1.summable (by simp [gKernel])
    rwa [hF1.tsum_eq] at h
  have h3b : (∑ d ∈ D, gKernel d * Real.log (d : ℝ)) =
      (∑' d : ℕ, if Nat.Coprime d m then gKernel d * Real.log (d : ℝ) else 0) -
        ∑' d : ℕ, if x < (d : ℝ) then
          (if Nat.Coprime d m then gKernel d * Real.log (d : ℝ) else 0) else 0 :=
    hsplit (fun d ↦ gKernel d * Real.log (d : ℝ)) hCgL (by simp [gKernel])
  set Qfull : ℝ := ∑' d : ℕ, if Nat.Coprime d m then gKernel d * Real.log d else 0 with hQdef
  set Tg : ℝ := ∑' d : ℕ, if x < (d : ℝ) then (if Nat.Coprime d m then gKernel d else 0) else 0
    with hTgdef
  set TgL : ℝ := ∑' d : ℕ, if x < (d : ℝ) then
      (if Nat.Coprime d m then gKernel d * Real.log (d : ℝ) else 0) else 0 with hTgLdef
  have hE : E = (Real.log x + γ + ellV m) * Tg - TgL := by
    have hpt : ∀ d : ℕ, (if ((x < (d : ℝ)) ∧ Nat.Coprime d m) then
            gKernel d * (Real.log (x / d) + γ + ellV m) else 0) =
          (Real.log x + γ + ellV m) *
              (if x < (d : ℝ) then (if Nat.Coprime d m then gKernel d else 0) else 0) -
            (if x < (d : ℝ) then
              (if Nat.Coprime d m then gKernel d * Real.log (d : ℝ) else 0) else 0) := by
      intro d
      by_cases hxd : x < (d : ℝ)
      · have hlogdiv : Real.log (x / d) = Real.log x - Real.log (d : ℝ) :=
          Real.log_div hxpos.ne' (hxpos.trans hxd).ne'
        rw [if_pos hxd, if_pos hxd]
        by_cases hcop : Nat.Coprime d m
        · rw [if_pos ⟨hxd, hcop⟩, if_pos hcop, if_pos hcop, hlogdiv]; ring
        · rw [if_neg (fun h ↦ hcop h.2), if_neg hcop, if_neg hcop]; ring
      · rw [if_neg (fun h ↦ hxd h.1), if_neg hxd, if_neg hxd]; ring
    rw [hEdef, hTgdef, hTgLdef, tsum_congr hpt,
      Summable.tsum_sub ((summable_ite_zero hF1.summable).mul_left _) (summable_ite_zero hCgL),
      tsum_mul_left]
  have hconvR : conv - R = L * ∑ d ∈ D, gKernel d * P d := by
    rw [hconvdef, hRdef, ← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun d _ ↦ by simp only [hPdef]; ring
  have hDsum : (∑ d ∈ D, gKernel d * P d) = (Real.log x + γ + ellV m) * (∑ d ∈ D, gKernel d) -
        (∑ d ∈ D, gKernel d * Real.log (d : ℝ)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1.1
    simp only [hPdef]
    rw [Real.log_div hxpos.ne' (by linarith : (0 : ℝ) < (d : ℝ)).ne']
    ring
  rw [hDsum, h3a, h3b] at hconvR
  rw [hE]
  have : conv - R = L * ((Real.log x + γ + ellV m) - Qfull -
      ((Real.log x + γ + ellV m) * Tg - TgL)) := by
    rw [hconvR]; ring
  linarith only [this]

/-- The Euler–Mascheroni term `φ(m)/m · (γ − ∑_{(d,m)=1} g(d) log d)` is `O(φ(m)/m)`. -/
private lemma exists_abs_density_mul_euler_sub_kernelLogSum_le : ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m →
      |(Nat.totient m : ℝ) / m * (Real.eulerMascheroniConstant -
          ∑' d : ℕ, if Nat.Coprime d m then gKernel d * Real.log d else 0)| ≤
        C * ((Nat.totient m : ℝ) / m) := by
  classical
  obtain ⟨CC, hCC, hCCsummable, hCCsum, -⟩ := gKernel_logtail_bound
  refine ⟨1 + CC, by linarith only [hCC], ?_⟩
  intro m hm
  set L : ℝ := (Nat.totient m : ℝ) / m with hLdef
  set γ : ℝ := Real.eulerMascheroniConstant with hγdef
  set Qfull : ℝ := ∑' d : ℕ, if Nat.Coprime d m then gKernel d * Real.log d else 0 with hQdef
  have hL_pos : 0 < L := totient_div_self_pos hm
  have hγ_bound : |γ| ≤ 1 := by
    rw [hγdef, abs_of_nonneg (by linarith only [Real.one_half_lt_eulerMascheroniConstant])]
    linarith only [Real.eulerMascheroniConstant_lt_two_thirds]
  have hQ_bound : |Qfull| ≤ CC := by
    rw [← Real.norm_eq_abs, hQdef]
    exact (tsum_of_norm_bounded hCCsummable.hasSum
      (norm_ite_coprime_gKernel_mul_log_le m)).trans hCCsum
  have hsub_bound : |γ - Qfull| ≤ 1 + CC := by
    rw [sub_eq_add_neg]
    refine (abs_add_le _ _).trans ?_
    rw [abs_neg]
    linarith only [hγ_bound, hQ_bound]
  rw [abs_mul, abs_of_pos hL_pos, mul_comm (1 + CC) L]
  exact mul_le_mul_of_nonneg_left hsub_bound hL_pos.le

/-- Pointwise domination for the tail correction: for `d > x` the term
`g(d)·(log (x/d) + γ + ℓ(m))` is bounded in norm by `|g(d)|·log (d/x) + (γ + ℓ(m))·|g(d)|`,
and for `d ≤ x` the left-hand side vanishes. -/
private lemma norm_ite_gt_coprime_gKernel_mul_shiftedLog_le (m d : ℕ) (x : ℝ) (hxpos : 0 < x) :
    ‖(if ((x < (d : ℝ)) ∧ Nat.Coprime d m) then
        gKernel d * (Real.log (x / d) + Real.eulerMascheroniConstant + ellV m) else 0)‖ ≤
      (if x ≤ (d : ℝ) then |gKernel d| * Real.log ((d : ℝ) / x) else 0) +
        (Real.eulerMascheroniConstant + ellV m) *
          (if x ≤ (d : ℝ) then |gKernel d| else 0) := by
  set γ : ℝ := Real.eulerMascheroniConstant with hγdef
  set c : ℝ := γ + ellV m with hcdef
  have hγ_nonneg : 0 ≤ γ := by
    have : (1 : ℝ) / 2 < γ := by rw [hγdef]; exact Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hc_nonneg : 0 ≤ c := by rw [hcdef]; linarith only [hγ_nonneg, ellV_nonneg m]
  have hlogdx_nonneg : x ≤ (d : ℝ) → 0 ≤ Real.log ((d : ℝ) / x) := fun hd ↦
    Real.log_nonneg (by rw [le_div_iff₀ hxpos]; linarith)
  have hRHS_nonneg : 0 ≤ (if x ≤ (d : ℝ) then |gKernel d| * Real.log ((d : ℝ) / x) else 0) +
      c * (if x ≤ (d : ℝ) then |gKernel d| else 0) := by
    have h1 : 0 ≤ if x ≤ (d : ℝ) then |gKernel d| * Real.log ((d : ℝ) / x) else 0 := by
      split_ifs with hd
      · exact mul_nonneg (abs_nonneg _) (hlogdx_nonneg hd)
      · exact le_rfl
    have h2 : 0 ≤ if x ≤ (d : ℝ) then |gKernel d| else 0 := by split_ifs <;> positivity
    linarith only [h1, mul_nonneg hc_nonneg h2]
  by_cases hcase : (x < (d : ℝ)) ∧ Nat.Coprime d m
  · obtain ⟨hxd, hcop⟩ := hcase
    rw [if_pos ⟨hxd, hcop⟩, if_pos hxd.le, if_pos hxd.le, Real.norm_eq_abs, abs_mul]
    have hlogswap : Real.log (x / (d : ℝ)) = -Real.log ((d : ℝ) / x) := by
      rw [← Real.log_inv, inv_div]
    have habs : |Real.log (x / d) + γ + ellV m| ≤ Real.log ((d : ℝ) / x) + c := by
      rw [hlogswap, abs_le]
      constructor <;> linarith only [hcdef, hc_nonneg, hlogdx_nonneg hxd.le]
    calc |gKernel d| * |Real.log (x / d) + γ + ellV m|
        ≤ |gKernel d| * (Real.log ((d : ℝ) / x) + c) :=
          mul_le_mul_of_nonneg_left habs (abs_nonneg _)
      _ = |gKernel d| * Real.log ((d : ℝ) / x) + c * |gKernel d| := by ring
  · rw [if_neg hcase, norm_zero]
    exact hRHS_nonneg

/-- The tail correction `φ(m)/m · ∑_{d > x, (d,m)=1} g(d)·(log (x/d) + γ + ℓ(m))` is
`O(τ(m) · log (2mx) / √x)`. -/
private lemma exists_abs_density_mul_tailSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → Squarefree m → ∀ x : ℝ, 2 ≤ x →
      |(Nat.totient m : ℝ) / m * (∑' d : ℕ, if ((x < (d : ℝ)) ∧ Nat.Coprime d m) then
          gKernel d * (Real.log (x / d) + Real.eulerMascheroniConstant + ellV m) else 0)| ≤
        C * ((#m.divisors : ℝ) * Real.log (2 * m * x) / √x) := by
  classical
  obtain ⟨CB, hCB, hLEMB⟩ := gKernel_tail_bound
  obtain ⟨CC, hCC, hCCsummable, -, hLEMC⟩ := gKernel_logtail_bound
  refine ⟨CC + 2 * CB, by linarith only [hCB, hCC], ?_⟩
  intro m hm hsq x hx
  set L : ℝ := (Nat.totient m : ℝ) / m with hLdef
  set γ : ℝ := Real.eulerMascheroniConstant with hγdef
  set E : ℝ := ∑' d : ℕ, if ((x < (d : ℝ)) ∧ Nat.Coprime d m) then
        gKernel d * (Real.log (x / d) + γ + ellV m) else 0
    with hEdef
  have hxpos : (0 : ℝ) < x := by linarith
  have hsqrtx : (0 : ℝ) < √x := Real.sqrt_pos.mpr hxpos
  have hL_pos : 0 < L := totient_div_self_pos hm
  have hL_le_one : L ≤ 1 := totient_div_self_le_one hm
  have htau_pos : (1 : ℝ) ≤ (#m.divisors : ℝ) := one_le_cast_card_divisors hm
  have hγ_nonneg : 0 ≤ γ := by
    have : (1 : ℝ) / 2 < γ := by rw [hγdef]; exact Real.one_half_lt_eulerMascheroniConstant
    linarith
  have hell_le_tau' : ellV m ≤ (#m.divisors : ℝ) := ellV_le_tau m hsq
  set B1 : ℝ := ∑' d : ℕ, if x ≤ (d : ℝ) then |gKernel d| * Real.log ((d : ℝ) / x) else 0
    with hB1def
  set B2 : ℝ := ∑' d : ℕ, if x ≤ (d : ℝ) then |gKernel d| else 0 with hB2def
  have hB1 : B1 ≤ CC * Real.log (2 * x) / √x := by
    rw [hB1def]; exact hLEMC x (by linarith)
  have hB2 : B2 ≤ CB * Real.log (2 * x) / √x := by
    rw [hB2def]; exact hLEMB x (by linarith)
  have hB1_summand_nonneg : ∀ d : ℕ,
      (0 : ℝ) ≤ if x ≤ (d : ℝ) then |gKernel d| * Real.log ((d : ℝ) / x) else 0 := fun d ↦ by
    split_ifs with hd
    · exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by rw [le_div_iff₀ hxpos]; linarith))
    · exact le_rfl
  have hsummB1 : Summable (fun d : ℕ ↦
      if x ≤ (d : ℝ) then |gKernel d| * Real.log ((d : ℝ) / x) else 0) := by
    refine Summable.of_nonneg_of_le hB1_summand_nonneg ?_
      (summable_ite_zero (P := fun d : ℕ ↦ x ≤ (d : ℝ)) hCCsummable)
    intro d; split_ifs with hd
    · have hd1 : (1 : ℝ) ≤ (d : ℝ) := by linarith
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      refine Real.log_le_log (by rw [lt_div_iff₀ hxpos]; linarith only [hd1]) ?_
      rw [div_le_iff₀ hxpos]
      linarith only [mul_nonneg (by linarith only [hd1] : (0 : ℝ) ≤ (d : ℝ))
        (by linarith only [hx] : (0 : ℝ) ≤ 2 * x - 1)]
    · exact le_rfl
  have hsummB2 : Summable (fun d : ℕ ↦ if x ≤ (d : ℝ) then |gKernel d| else 0) :=
    summable_ite_zero (gKernel_norm_summable.congr fun d ↦ Real.norm_eq_abs _)
  have hB1_nonneg : 0 ≤ B1 := by rw [hB1def]; exact tsum_nonneg hB1_summand_nonneg
  have hB2_nonneg : 0 ≤ B2 := by
    rw [hB2def]; exact tsum_nonneg fun d ↦ by split_ifs <;> positivity
  set c : ℝ := γ + ellV m with hcdef
  have hc_nonneg : 0 ≤ c := by rw [hcdef]; linarith only [hγ_nonneg, ellV_nonneg m]
  have hHasSum : HasSum
      (fun d : ℕ ↦ (if x ≤ (d : ℝ) then |gKernel d| * Real.log ((d : ℝ) / x) else 0) +
        c * (if x ≤ (d : ℝ) then |gKernel d| else 0))
      (B1 + c * B2) := by
    have := (hsummB1.hasSum).add ((hsummB2.hasSum).mul_left c)
    rwa [← hB1def, ← hB2def] at this
  have hEbound : |E| ≤ B1 + c * B2 := by
    rw [hEdef, ← Real.norm_eq_abs]
    exact tsum_of_norm_bounded hHasSum fun d ↦
      norm_ite_gt_coprime_gKernel_mul_shiftedLog_le m d x hxpos
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hlog_mono : Real.log (2 * x) ≤ Real.log (2 * m * x) :=
    Real.log_le_log (by linarith) (by linarith only [mul_nonneg hxpos.le (sub_nonneg.mpr hm1)])
  have hlogmx_nonneg : 0 ≤ Real.log (2 * m * x) :=
    (Real.log_nonneg (by linarith)).trans hlog_mono
  set T : ℝ := (#m.divisors : ℝ) * Real.log (2 * m * x) / √x with hTdef
  have hB1'' : B1 ≤ CC * T := by
    refine hB1.trans ?_
    rw [hTdef, mul_div_assoc, mul_div_assoc, ← mul_div_assoc (a := (#m.divisors : ℝ))]
    refine mul_le_mul_of_nonneg_left ?_ hCC.le
    rw [div_le_div_iff_of_pos_right hsqrtx]
    exact hlog_mono.trans (le_mul_of_one_le_left hlogmx_nonneg htau_pos)
  have hB2' : B2 ≤ CB * (Real.log (2 * m * x) / √x) := by
    refine hB2.trans ?_
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (by rw [div_le_div_iff_of_pos_right hsqrtx]; exact hlog_mono) hCB.le
  have hc_le : c ≤ 2 * (#m.divisors : ℝ) := by
    rw [hcdef, hγdef]
    linarith only [Real.eulerMascheroniConstant_lt_two_thirds, hell_le_tau', htau_pos]
  calc |L * E| = L * |E| := by rw [abs_mul, abs_of_pos hL_pos]
    _ ≤ L * (B1 + c * B2) := mul_le_mul_of_nonneg_left hEbound hL_pos.le
    _ ≤ 1 * (B1 + c * B2) := mul_le_mul_of_nonneg_right hL_le_one
        (by linarith only [hB1_nonneg, mul_nonneg hc_nonneg hB2_nonneg])
    _ = B1 + c * B2 := one_mul _
    _ ≤ CC * T + (2 * (#m.divisors : ℝ)) * (CB * (Real.log (2 * m * x) / √x)) :=
        add_le_add hB1'' ((mul_le_mul_of_nonneg_right hc_le hB2_nonneg).trans
          (mul_le_mul_of_nonneg_left hB2' (by positivity)))
    _ = (CC + 2 * CB) * ((#m.divisors : ℝ) * Real.log (2 * m * x) / √x) := by
        rw [hTdef]; ring

/-- The remainder `∑_{d ≤ x, (d,m)=1} g(d) · (error of the inner coprime harmonic sum at x/d)`
is `O(τ(m) · log (2mx) / √x)`. -/
private lemma exists_abs_kernelErrorSum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 1 ≤ m → Squarefree m → ∀ x : ℝ, 2 ≤ x →
      |∑ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m),
          gKernel d * (coprimeReciprocalSum m (x / d) - (Nat.totient m : ℝ) / m *
            (Real.log (x / d) + Real.eulerMascheroniConstant + ellV m))| ≤
        C * ((#m.divisors : ℝ) * Real.log (2 * m * x) / √x) := by
  classical
  obtain ⟨C0, hC0, hF5⟩ := coprime_reciprocal_sum_asymptotic
  obtain ⟨CA, hCA, hLEMA⟩ := gKernel_partial_weighted_bound
  refine ⟨2 * √2 * C0 * CA, by positivity, ?_⟩
  intro m hm hsq x hx
  set L : ℝ := (Nat.totient m : ℝ) / m with hLdef
  set γ : ℝ := Real.eulerMascheroniConstant
  set D : Finset ℕ := (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m) with hDdef
  set R : ℝ := ∑ d ∈ D,
      gKernel d * (coprimeReciprocalSum m (x / d) - L * (Real.log (x / d) + γ + ellV m))
    with hRdef
  have hxpos : (0 : ℝ) < x := by linarith
  have hxfloor_le : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hxpos.le
  set err : ℕ → ℝ := fun d ↦
    coprimeReciprocalSum m (x / d) - L * (Real.log (x / d) + γ + ellV m) with herrdef
  have hstep1 : |R| ≤ ∑ d ∈ D, |gKernel d| * |err d| :=
    calc |R| = |∑ d ∈ D, gKernel d * err d| := by rw [hRdef]
      _ ≤ ∑ d ∈ D, |gKernel d * err d| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ d ∈ D, |gKernel d| * |err d| := by simp_rw [abs_mul]
  have hcoef_nonneg : (0 : ℝ) ≤ C0 * (#m.divisors : ℝ) / x := by positivity
  have hterm : ∀ d ∈ D, |gKernel d| * |err d| ≤
      (C0 * (#m.divisors : ℝ) / x) * (|gKernel d| * (d : ℝ)) := by
    intro d hd
    rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hdpos, hdle⟩, -⟩ := hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hdpos
    have hdleR : (d : ℝ) ≤ x := (by exact_mod_cast hdle : (d : ℝ) ≤ (⌊x⌋₊ : ℝ)).trans hxfloor_le
    have herr_bound : |err d| ≤ C0 * (#m.divisors : ℝ) / x * (d : ℝ) := by
      have hf := hF5 m hm hsq (x / (d : ℝ)) (by rw [le_div_iff₀ (by linarith)]; linarith)
      have hrw : C0 * ((#m.divisors : ℝ) / (x / (d : ℝ))) =
          C0 * (#m.divisors : ℝ) / x * (d : ℝ) := by rw [div_div_eq_mul_div]; ring
      have hlhs : err d = coprimeReciprocalSum m (x / (d : ℝ)) -
          (Nat.totient m : ℝ) / m * (Real.log (x / (d : ℝ)) + γ + ellV m) := by
        rw [herrdef, hLdef]
      rw [hrw] at hf
      rwa [hlhs]
    calc |gKernel d| * |err d| ≤ |gKernel d| * (C0 * (#m.divisors : ℝ) / x * (d : ℝ)) :=
          mul_le_mul_of_nonneg_left herr_bound (abs_nonneg _)
      _ = (C0 * (#m.divisors : ℝ) / x) * (|gKernel d| * (d : ℝ)) := by ring
  have hstep2 : (∑ d ∈ D, |gKernel d| * |err d|) ≤
      (C0 * (#m.divisors : ℝ) / x) * (∑ d ∈ D, |gKernel d| * (d : ℝ)) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hterm
  have hsubset : D ⊆ Finset.Icc 1 ⌈x⌉₊ := fun d hd ↦ by
    rw [hDdef, Finset.mem_filter, Finset.mem_Icc] at hd
    exact Finset.mem_Icc.mpr ⟨hd.1.1, hd.1.2.trans (Nat.floor_le_ceil x)⟩
  have hstep3 : (∑ d ∈ D, |gKernel d| * (d : ℝ)) ≤ ∑ d ∈ Finset.Icc 1 ⌈x⌉₊, |gKernel d| * (d : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun d _ _ ↦ mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hceil_ge : x ≤ (⌈x⌉₊ : ℝ) := Nat.le_ceil x
  have hceil_le : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
    have h1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith
  have hsqrt_bound : √(⌈x⌉₊ : ℝ) ≤ √2 * √x := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    exact Real.sqrt_le_sqrt hceil_le
  have hlogmx_nonneg : 0 ≤ Real.log (2 * m * x) := Real.log_nonneg (by
    linarith only [mul_nonneg (sub_nonneg.mpr hm1) (by linarith only [hx] : (0 : ℝ) ≤ x - 2),
      hx, hm1])
  have hlog_bound : Real.log (2 * (⌈x⌉₊ : ℝ)) ≤ 2 * Real.log (2 * m * x) := by
    have hsq : 4 * x ≤ (2 * m * x) ^ 2 := by
      have hm2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by
        rw [pow_two]
        exact hm1.trans (le_mul_of_one_le_right (by linarith only [hm1]) hm1)
      have h1 : (1 : ℝ) ≤ (m : ℝ) ^ 2 * x :=
        (by linarith only [hx] : (1 : ℝ) ≤ x).trans
          (le_mul_of_one_le_left (by linarith only [hx]) hm2)
      linarith only [mul_nonneg hxpos.le (sub_nonneg.mpr h1)]
    calc Real.log (2 * (⌈x⌉₊ : ℝ)) ≤ Real.log (4 * x) := Real.log_le_log (by linarith) (by linarith)
      _ ≤ Real.log ((2 * m * x) ^ 2) := Real.log_le_log (by linarith only [hxpos]) hsq
      _ = 2 * Real.log (2 * m * x) := by rw [Real.log_pow]; push_cast; ring
  have hRHS_bound : (∑ d ∈ Finset.Icc 1 ⌈x⌉₊, |gKernel d| * (d : ℝ)) ≤
      CA * (√2 * √x) * (2 * Real.log (2 * m * x)) :=
    (hLEMA ⌈x⌉₊).trans (mul_le_mul (mul_le_mul_of_nonneg_left hsqrt_bound hCA.le)
      hlog_bound (Real.log_nonneg (by linarith)) (by positivity))
  refine le_trans (hstep1.trans (hstep2.trans
    (mul_le_mul_of_nonneg_left (hstep3.trans hRHS_bound) hcoef_nonneg))) (le_of_eq ?_)
  rw [eq_comm, mul_div_assoc]
  field_simp
  rw [Real.sq_sqrt hxpos.le]
  ring

/-- The hyperbola sum `∑_{d ≤ x, (d, m) = 1} g(d) · ∑_{k ≤ x/d, (k, m) = 1} 1/k` equals
`φ(m)/m · (log x + ℓ(m))` up to `O(φ(m)/m + τ(m)·log (2mx)/√x)`. -/
lemma conv_asymptotic : ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → Squarefree m → ∀ (x : ℝ), 2 ≤ x →
      |(∑ d ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun d : ℕ ↦ Nat.Coprime d m),
            gKernel d * coprimeReciprocalSum m (x / d)) -
          (Nat.totient m : ℝ) / m * (Real.log x + ellV m)| ≤ C * ((Nat.totient m : ℝ) / m +
            (#m.divisors : ℝ) * Real.log (2 * m * x) / √x) := by
  classical
  obtain ⟨CG, hCG, hboundG⟩ := exists_abs_density_mul_euler_sub_kernelLogSum_le
  obtain ⟨CE, hCE, hboundE⟩ := exists_abs_density_mul_tailSum_le
  obtain ⟨CR, hCR, hboundR⟩ := exists_abs_kernelErrorSum_le
  refine ⟨CG + CE + CR, by linarith only [hCG, hCE, hCR], ?_⟩
  intro m hm hsq x hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hbudget1_nonneg : (0 : ℝ) ≤ (Nat.totient m : ℝ) / m := (totient_div_self_pos hm).le
  have hbudget2_nonneg : (0 : ℝ) ≤ (#m.divisors : ℝ) * Real.log (2 * m * x) / √x := by
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    refine div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg ?_)) (Real.sqrt_nonneg x)
    linarith only [mul_nonneg (sub_nonneg.mpr hm1) (by linarith only [hx] : (0 : ℝ) ≤ x - 2), hx,
      hm1]
  have habs_sub : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b ↦ by
    simpa [sub_eq_add_neg, abs_neg] using abs_add_le a (-b)
  rw [conv_sub_main_eq m x hxpos]
  refine le_trans (abs_add_le _ _) ?_
  refine le_trans (add_le_add (habs_sub _ _) le_rfl) ?_
  linarith only [hboundG m hm, hboundE m hm hsq x hx, hboundR m hm hsq x hx,
    mul_nonneg hCG.le hbudget2_nonneg,
    mul_nonneg hCE.le hbudget1_nonneg, mul_nonneg hCR.le hbudget1_nonneg]

/-- The Mertens-type asymptotic for coprime squarefree density: for squarefree `m ≥ 1` and `x ≥ 2`,
`A(m, x) = ∑_{n ≤ x, (n, m) = 1} μ(n)²/φ(n)` equals `φ(m)/m · (log x + ℓ(m))` up to an error
`O(φ(m)/m + τ(m)·log (2mx)/√x)`, with an absolute implied constant. -/
@[pg_tag "bg246" "slem_coprime_density"]
theorem exists_abs_sumA_sub_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (m : ℕ), 1 ≤ m → Squarefree m → ∀ (x : ℝ), 2 ≤ x →
      |PrimeGaps.MaynardOffDiagonal.sumA m x - (Nat.totient m : ℝ) / m * (Real.log x + ellV m)| ≤
        C * ((Nat.totient m : ℝ) / m +
            (#m.divisors : ℝ) * Real.log (2 * m * x) / √x) := by
  obtain ⟨C, hC, hbound⟩ := conv_asymptotic
  refine ⟨C, hC, fun m hm hsq x hx ↦ ?_⟩
  rw [sumA_eq_conv m x]
  exact hbound m hm hsq x hx

end PrimeGaps
