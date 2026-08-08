/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.SumIntegralComparisons
public import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
public import PrimeGapsTheory.ForMathlib.Topology.Algebra.InfiniteSum.Defs


/-!
# Facts about Riemann's zeta function

On the real half-line `σ > 1` we record the Dirichlet series for `ζ`, the bounds
`1 < ζ(σ) ≤ σ / (σ - 1)`, and the resulting bound `∑_p p ^ (-σ) ≤ log ζ(σ)` on the prime zeta
function, together with the summability criteria for `∑_p p ^ (-s)` over the primes.
-/

@[expose] public section

open Real Complex Finset Nat
open ArithmeticFunction

theorem hasSum_riemannZeta {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℂ) ^ s) (riemannZeta s) := by
  convert (summable_one_div_nat_cpow.mpr hs).hasSum
  exact zeta_eq_tsum_one_div_nat_cpow hs

theorem hasSum_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    HasSum (fun n : ℕ ↦ 1 / (n : ℝ) ^ σ) (riemannZeta σ).re := by
  convert hasSum_re <| hasSum_riemannZeta (s := σ) (by simpa) with n
  rw [← ofReal_natCast, ← ofReal_cpow (by positivity), ← ofReal_one, ← ofReal_div, ofReal_re]

theorem re_riemannZeta_eq_tsum_one_div_rpow {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re = ∑' n : ℕ, 1 / (n : ℝ) ^ σ :=
  (hasSum_re_riemannZeta hσ).tsum_eq.symm

theorem one_lt_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) : 1 < (riemannZeta σ).re := by
  have hrange : (1 : ℝ) < ∑ n ∈ range 3, 1 / (n : ℝ) ^ σ := by
    simpa [sum_range_succ, zero_rpow (by positivity : σ ≠ 0)] using
      lt_add_of_pos_right (1 : ℝ) (one_div_pos.mpr <| rpow_pos_of_pos two_pos σ)
  exact hrange.trans_le <| sum_le_hasSum _
    (fun _ _ ↦ one_div_nonneg.mpr <| rpow_nonneg (by positivity) _) (hasSum_re_riemannZeta hσ)

theorem summable_vonMangoldt_div_pow_mul_log {σ : ℝ} (hσ : 1 < σ) :
    Summable fun n ↦ Λ n / (n ^ σ * Real.log n) := by
  refine .of_tsum_ne_zero <| ne_of_gt ?_
  rw [← log_riemannZeta_eq hσ]
  exact log_pos <| one_lt_re_riemannZeta hσ

theorem re_riemannZeta_le_div_sub_one {σ : ℝ} (hσ : 1 < σ) : (riemannZeta σ).re ≤ σ / (σ - 1) := by
  have hintegrable := integrableOn_Ioi_rpow_of_lt (neg_lt_neg hσ) one_pos
  have hcomp := AntitoneOn.tsum_comp_add_le_integral 1 ((antitoneOn_rpow_Ioi_of_exponent_nonpos
    (neg_nonpos.mpr (by positivity))).mono (Set.Ici_subset_Ioi.mpr (by positivity)))
    (by norm_cast) fun _ _ ↦ rpow_nonneg (by grind) _
  rw [re_riemannZeta_eq_tsum_one_div_rpow hσ,
    ← Summable.sum_add_tsum_nat_add 2 (summable_one_div_nat_rpow.mpr hσ)]
  simp_rw [← inv_eq_one_div, ← rpow_neg (Nat.cast_nonneg _)]
  grw [hcomp, integral_Ioi_rpow_of_lt (by grind) (by positivity)]
  suffices 1 + -1 / (-σ + 1) = σ / (σ - 1) by
    simp [sum_range_succ, zero_rpow (by grind : -σ ≠ 0), this]
  grind

theorem log_re_riemannZeta_le_log_sub_log_sub_one {σ : ℝ} (hσ : 1 < σ) :
    (riemannZeta σ).re.log ≤ σ.log - (σ - 1).log := by
  grw [re_riemannZeta_le_div_sub_one hσ, log_div (by positivity) (by positivity)]
  · exact riemannZeta_re_pos_of_one_lt hσ

theorem Real.summable_one_div_prime_rpow {σ : ℝ} :
    Summable (fun p : Primes ↦ 1 / (p : ℝ) ^ σ) ↔ 1 < σ := by
  by_cases! hσ : 1 < σ
  · simp only [hσ, iff_true]
    exact (summable_one_div_nat_rpow.mpr hσ).subtype Nat.Prime
  · simp only [hσ.not_gt, iff_false]
    exact fun H ↦ Primes.not_summable_one_div <| H.of_nonneg_of_le (fun _ ↦ by positivity)
      fun p ↦ one_div_le_one_div_of_le (by positivity [p.2.ne_zero]) <|
        rpow_le_self_of_one_le (by simpa using p.2.one_le) hσ

theorem Complex.summable_one_div_prime_cpow {s : ℂ} :
    Summable (fun p : Primes ↦ 1 / (p : ℂ) ^ s) ↔ 1 < s.re := by
  rw [← summable_one_div_prime_rpow, ← summable_norm_iff]
  simp [norm_cpow_eq_rpow_re_of_pos, ← ofReal_natCast,
    show ∀ p : Primes, 0 < (p : ℝ) by simpa using fun p ↦ p.2.pos]

theorem tsum_prime_rpow_le_log_re_riemannZeta {σ : ℝ} (hσ : 1 < σ) :
    ∑' p : Primes, (1 / p ^ σ : ℝ) ≤ (riemannZeta σ).re.log := by
  rw [Primes.tsum_eq_tsum_ite fun n : ℕ ↦ 1 / (n : ℝ) ^ σ, log_riemannZeta_eq hσ]
  refine Summable.tsum_le_tsum (fun p ↦ ?_)
    ((Primes.summable_iff_summable_ite _).mp <| summable_one_div_prime_rpow.mpr hσ)
    (summable_vonMangoldt_div_pow_mul_log hσ)
  split_ifs with hp
  · rw [vonMangoldt_apply_prime hp, ← inv_eq_one_div,
      div_mul_cancel_right₀ (ne_of_gt <| log_pos <| by simp [hp.one_lt])]
  · positivity
