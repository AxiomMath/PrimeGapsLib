/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.PSeries
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Log.Monotone
public import Mathlib.Analysis.SumIntegralComparisons

/-!
# The series and integral of `log x / x ^ 2`

Summability, antitonicity, the improper integral over `Ioi m`, and the resulting tail bound
for the integrand `log x / x ^ 2`. This is the single substrate for the `log / square` estimates
used by the removed-primes bound and by the truncated-sieve decomposition.

## Main results

* `Real.summable_log_div_sq`: `∑ log n / n ^ 2` converges.
* `Real.log_div_sq_antitoneOn`: `log x / x ^ 2` is antitone on `Ici a` for `a ≥ 2`.
* `Real.integral_Ioi_log_div_sq`: `∫_{Ioi m} log x / x ^ 2 = (log m + 1) / m` for `m ≥ 1`.
* `Real.tail_log_div_sq_le`: `∑_{n > m} log n / n ^ 2 ≤ (log m + 1) / m` for `m ≥ 3`.
-/

@[expose] public section

open Real

open scoped Topology

namespace Real

/-- Summability of `log n / n^2` over the naturals. -/
theorem summable_log_div_sq : Summable (fun n : ℕ ↦ Real.log n / (n : ℝ) ^ 2) := by
  have hsum : Summable (fun n : ℕ ↦ 2 * (1 / (n : ℝ) ^ (3 / 2 : ℝ))) :=
    (Real.summable_one_div_nat_rpow.mpr (by norm_num)).mul_left 2
  refine Summable.of_nonneg_of_le
    (fun n ↦ div_nonneg (Real.log_natCast_nonneg n) (by positivity)) (fun n ↦ ?_) hsum
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
    have hlog : Real.log n ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) := by
      have := Real.log_natCast_le_rpow_div n (ε := 1 / 2) (by norm_num)
      rw [div_eq_mul_inv] at this
      simpa [mul_comm] using this
    calc Real.log n / (n : ℝ) ^ 2 ≤ 2 * (n : ℝ) ^ (1 / 2 : ℝ) / (n : ℝ) ^ 2 := by gcongr
      _ = 2 * (1 / (n : ℝ) ^ (3 / 2 : ℝ)) := by
          rw [show (n : ℝ) ^ 2 = (n : ℝ) ^ (2 : ℝ) by norm_num, mul_div_assoc,
            one_div ((n : ℝ) ^ (3 / 2 : ℝ)), ← Real.rpow_neg hnpos.le, ← Real.rpow_sub hnpos]
          norm_num

/-- `f x = log x / x²` is antitone on `Ici a` for `a ≥ 2`: the Mathlib bound
`Real.log_div_self_rpow_antitoneOn` gives antitonicity from `exp (1/2)` onwards, and `2` is
past that threshold. -/
theorem log_div_sq_antitoneOn (a : ℝ) (ha : 2 ≤ a) :
    AntitoneOn (fun x ↦ Real.log x / x ^ 2) (Set.Ici a) := by
  have hexp : rexp (2 : ℝ)⁻¹ ≤ 2 := by
    have h1 : rexp (2 : ℝ)⁻¹ * rexp (2 : ℝ)⁻¹ = rexp 1 := by
      rw [← Real.exp_add]
      norm_num
    nlinarith [Real.exp_one_lt_d9, Real.exp_pos (2 : ℝ)⁻¹]
  simpa only [Real.rpow_two] using (Real.log_div_self_rpow_antitoneOn (a := 2) two_pos).mono
    (Set.Ici_subset_Ici.mpr (hexp.trans ha))

/-- The antiderivative computation: `∫_{Ioi m} log x / x² = (log m + 1)/m` for `m ≥ 1`. -/
theorem integral_Ioi_log_div_sq (m : ℝ) (hm : 1 ≤ m) :
    ∫ x in Set.Ioi m, Real.log x / x ^ 2 = (Real.log m + 1) / m := by
  have hmpos : (0 : ℝ) < m := by linarith
  set g : ℝ → ℝ := fun x ↦ -(Real.log x + 1) / x with hg
  have hderiv : ∀ x ∈ Set.Ioi m, HasDerivAt g (Real.log x / x ^ 2) x := by
    intro x hx
    have hxne : x ≠ 0 := (hmpos.trans hx).ne'
    have hnum : HasDerivAt (fun x ↦ -(Real.log x + 1)) (-(1 / x)) x :=
      HasDerivAt.neg (by simpa using (Real.hasDerivAt_log hxne).add_const 1)
    have hden : HasDerivAt (fun x : ℝ ↦ x) (1 : ℝ) x := hasDerivAt_id x
    have hdiv := hnum.div hden hxne
    rw [show (-(1 / x) * x - -(Real.log x + 1) * 1) / x ^ 2 = Real.log x / x ^ 2 by
      field_simp
      ring] at hdiv
    exact hdiv
  have hg'pos : ∀ x ∈ Set.Ioi m, 0 ≤ Real.log x / x ^ 2 := fun x hx ↦
    div_nonneg (Real.log_nonneg (hm.trans hx.le)) (by positivity)
  have hcont : ContinuousWithinAt g (Set.Ici m) m :=
    ContinuousWithinAt.div
      ((Real.continuousAt_log hmpos.ne').continuousWithinAt.add continuousWithinAt_const).neg
      continuousWithinAt_id hmpos.ne'
  have htend : Filter.Tendsto g Filter.atTop (𝓝 0) := by
    have h1 : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x) Filter.atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
    have h2 : Filter.Tendsto (fun x : ℝ ↦ (1 : ℝ) / x) Filter.atTop (𝓝 0) :=
      Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
    have hcomb : Filter.Tendsto (fun x : ℝ ↦ -(Real.log x / x) - 1 / x) Filter.atTop (𝓝 0) := by
      simpa using h1.neg.sub h2
    refine hcomb.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
    rw [hg]
    field_simp
    ring
  rw [MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hg'pos htend]
  simp only [hg]
  have hmne : m ≠ 0 := hmpos.ne'
  field_simp
  ring

/-- Tail bound: `∑_{e > m} log e / e² ≤ (log m + 1)/m` for `m ≥ 3`. -/
theorem tail_log_div_sq_le (m : ℕ) (hm : 3 ≤ m) :
    ∑' (n : ℕ), Real.log ((n + m + 1 : ℕ) : ℝ) / ((n + m + 1 : ℕ) : ℝ) ^ 2 ≤
      (Real.log m + 1) / m := by
  have hmR : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : (0 : ℝ) < (m : ℝ) := by linarith
  set f : ℝ → ℝ := fun x ↦ Real.log x / x ^ 2 with hf
  have hanti : AntitoneOn f (Set.Ici (m : ℝ)) :=
    log_div_sq_antitoneOn (m : ℝ) (by linarith)
  have hnn : ∀ t ∈ Set.Ioi (m : ℝ), 0 ≤ f t := fun t ht ↦
    div_nonneg (Real.log_nonneg (by simp only [Set.mem_Ioi] at ht; linarith)) (by positivity)
  have hint : MeasureTheory.IntegrableOn f (Set.Ioi (m : ℝ)) MeasureTheory.volume := by
    have hg_int : MeasureTheory.IntegrableOn (fun x : ℝ ↦ 2 * x ^ (-3 / 2 : ℝ))
        (Set.Ioi (m : ℝ)) MeasureTheory.volume :=
      (integrableOn_Ioi_rpow_of_lt (a := (-3 / 2 : ℝ)) (c := (m : ℝ)) (by norm_num)
        hmpos).const_mul 2
    have hcontOn : ContinuousOn f (Set.Ioi (m : ℝ)) :=
      ContinuousOn.div (Real.continuousOn_log.mono fun x hx ↦ by
          simp only [Set.mem_Ioi] at hx
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          rintro rfl
          linarith)
        (continuous_pow 2).continuousOn fun x hx ↦ by
          simp only [Set.mem_Ioi] at hx
          have : (0 : ℝ) < x := by linarith
          positivity
    have hbound : ∀ᵐ x ∂(MeasureTheory.volume.restrict (Set.Ioi (m : ℝ))),
        ‖f x‖ ≤ 2 * x ^ (-3 / 2 : ℝ) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      filter_upwards with x hx
      simp only [Set.mem_Ioi] at hx
      have hxpos : (0 : ℝ) < x := by linarith
      rw [hf, Real.norm_eq_abs, abs_div, abs_of_nonneg (Real.log_nonneg (by linarith)),
        abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 2)]
      have hx2 : x ^ 2 = x ^ (2 : ℝ) := by
        rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      calc Real.log x / x ^ 2 ≤ (x ^ (1 / 2 : ℝ) / (1 / 2 : ℝ)) / x ^ 2 := by
            gcongr
            exact Real.log_le_rpow_div hxpos.le (by norm_num)
        _ = 2 * x ^ (-3 / 2 : ℝ) := by
            rw [hx2, show (-3 / 2 : ℝ) = 1 / 2 - 2 by norm_num, Real.rpow_sub hxpos]
            ring
    exact hg_int.mono' (hcontOn.aestronglyMeasurable measurableSet_Ioi) hbound
  have hcomp := AntitoneOn.tsum_comp_add_le_integral m hanti hint hnn
  rw [integral_Ioi_log_div_sq (m : ℝ) (by linarith)] at hcomp
  convert hcomp using 3 with n

end Real
