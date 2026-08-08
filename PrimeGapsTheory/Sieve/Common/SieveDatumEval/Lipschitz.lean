/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import PrimeGapsTheory.Arithmetic.PartialSummation
public import PrimeGapsTheory.Sieve.Common.SijD0.Basic
public import PrimeGapsTheory.Sieve.Transforms.YmSubstituteSmooth

/-!
# Lipschitz smoothing helpers

Kernel-integral bounds and the Lipschitz smooth approximation used by the partial-summation
estimates.

## Main results

* `lip_smooth_approx`
-/

@[expose] public section

open PrimeGaps MeasureTheory

/-- The average of `g` against a kernel `ker` of total mass one is bounded by `C` in absolute
value, given the pointwise bound `|ker u * g u| ≤ ker u * C`. -/
private theorem abs_integral_kernel_mul_le {ker g : ℝ → ℝ} {C : ℝ}
    (hkint : Integrable ker volume) (hkone : ∫ u, ker u = 1)
    (hint : Integrable (fun u ↦ ker u * g u) volume)
    (hbnd : ∀ u, |ker u * g u| ≤ ker u * C) :
    |∫ u, ker u * g u| ≤ C :=
  calc |∫ u, ker u * g u| ≤ ∫ u, |ker u * g u| := MeasureTheory.abs_integral_le_integral_abs
    _ ≤ ∫ u, ker u * C := MeasureTheory.integral_mono hint.abs (hkint.mul_const _) hbnd
    _ = C := by rw [MeasureTheory.integral_mul_const, hkone, one_mul]

/-- A differentiable function bounded by `M` and Lipschitz with constant `M` has `Gmax` at most
`2 * M`: the Lipschitz bound caps the derivative by `M` through the operator norm of the
differential, and `Gmax` is a supremum of `|f| + |deriv f|`. -/
private theorem Gmax_le_two_mul_of_bdd_of_lipschitz {f : ℝ → ℝ} {M : ℝ} (hM : 0 ≤ M)
    (hdiff : Differentiable ℝ f) (hbdd : ∀ t, |f t| ≤ M)
    (hlip : LipschitzWith (Real.toNNReal M) f) : Gmax f ≤ 2 * M :=
  ciSup_le fun t ↦ (add_le_add (hbdd t.val)
    (((hdiff t.val).hasDerivAt.le_of_lipschitz hlip).trans_eq
      (Real.coe_toNNReal M hM))).trans_eq (two_mul M).symm

/-- A globally `M` -bounded, `M` -Lipschitz function `H: ℝ → ℝ` admits a sequence of `C¹`
approximants `Hₙ` with `Gmax(Hₙ) ≤ 2M` and `Hₙ → H` uniformly at rate `M/(n+1)`.
-/
theorem lip_smooth_approx (H : ℝ → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hbdd : ∀ t, |H t| ≤ M) (hlip : ∀ s t, |H s - H t| ≤ M * |s - t|) :
    ∃ Hn : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 1 (Hn n)) ∧ (∀ n, Gmax (Hn n) ≤ 2 * M) ∧
      (∀ n t, |Hn n t - H t| ≤ M * (1 / (n + 1))) := by
  have hHcont : Continuous H :=
    LipschitzWith.continuous (K := Real.toNNReal M) <| .of_dist_le_mul fun s t ↦ by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal M hM]; exact hlip s t
  set φ : ℕ → ContDiffBump (0 : ℝ) := fun n ↦
    { rIn := 1 / (2 * (n + 1))
      rOut := 1 / (n + 1)
      rIn_pos := by positivity
      rIn_lt_rOut := by
        have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
        exact one_div_lt_one_div_of_lt h1 (by linarith) }
  set ψ : ℕ → ℝ → ℝ := fun n ↦ (φ n).normed volume
  set L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.lsmul ℝ ℝ
  set Hn : ℕ → ℝ → ℝ := fun n ↦ MeasureTheory.convolution (ψ n) H L volume
  have hψnn : ∀ n x, 0 ≤ ψ n x := fun n x ↦ (φ n).nonneg_normed x
  have hψint : ∀ n, ∫ x, ψ n x = 1 := fun n ↦ (φ n).integral_normed
  have hψintbl : ∀ n, Integrable (ψ n) volume := fun n ↦ (φ n).integrable_normed
  have hψcs : ∀ n, HasCompactSupport (ψ n) := fun n ↦ (φ n).hasCompactSupport_normed
  have hψsupp : ∀ n, Function.support (ψ n) = Metric.ball (0 : ℝ) (1 / (n + 1)) :=
    fun n ↦ (φ n).support_normed_eq
  have hval : ∀ n t, Hn n t = ∫ u, ψ n u * H (t - u) := fun _ _ ↦ rfl
  have hintegrand_int : ∀ n t, Integrable (fun u ↦ ψ n u * H (t - u)) volume := fun n t ↦
    (((φ n).continuous_normed).mul
      (hHcont.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      (hψcs n).mul_right
  have hcd : ∀ n, ContDiff ℝ 1 (Hn n) := fun n ↦
    (hψcs n).contDiff_convolution_left L (φ n).contDiff_normed hHcont.locallyIntegrable
  refine ⟨Hn, hcd, fun n ↦ ?_, fun n t ↦ ?_⟩
  · have hHn_bdd : ∀ t, |Hn n t| ≤ M := fun t ↦ by
      rw [hval n t]
      refine abs_integral_kernel_mul_le (hψintbl n) (hψint n) (hintegrand_int n t) fun u ↦ ?_
      rw [abs_mul, abs_of_nonneg (hψnn n u)]
      exact mul_le_mul_of_nonneg_left (hbdd _) (hψnn n u)
    have hHn_lip : LipschitzWith (Real.toNNReal M) (Hn n) := .of_dist_le_mul fun s t ↦ by
      have hsub : Integrable (fun u ↦ ψ n u * (H (s - u) - H (t - u))) volume := by
        simp only [mul_sub]
        exact (hintegrand_int n s).sub (hintegrand_int n t)
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal M hM, hval n s, hval n t,
        ← MeasureTheory.integral_sub (hintegrand_int n s) (hintegrand_int n t)]
      simp only [← mul_sub]
      refine abs_integral_kernel_mul_le (hψintbl n) (hψint n) hsub fun u ↦ ?_
      rw [abs_mul, abs_of_nonneg (hψnn n u)]
      refine mul_le_mul_of_nonneg_left ?_ (hψnn n u)
      simpa only [sub_sub_sub_cancel_right] using hlip (s - u) (t - u)
    exact Gmax_le_two_mul_of_bdd_of_lipschitz hM ((hcd n).differentiable one_ne_zero) hHn_bdd
      hHn_lip
  · have hintbl2 : Integrable (fun u ↦ ψ n u * H t) volume := (hψintbl n).mul_const _
    have hdiff : Hn n t - H t = ∫ u, ψ n u * (H (t - u) - H t) := by
      simp only [mul_sub]
      rw [MeasureTheory.integral_sub (hintegrand_int n t) hintbl2, hval n t,
        MeasureTheory.integral_mul_const, hψint n, one_mul]
    rw [hdiff]
    refine abs_integral_kernel_mul_le (hψintbl n) (hψint n)
      (by simp only [mul_sub]; exact (hintegrand_int n t).sub hintbl2) fun u ↦ ?_
    rw [abs_mul, abs_of_nonneg (hψnn n u)]
    rcases eq_or_ne (ψ n u) 0 with hu | hu
    · simp [hu]
    · refine mul_le_mul_of_nonneg_left ?_ (hψnn n u)
      have husupp : |u| < 1 / (n + 1) := by
        have h : u ∈ Metric.ball (0 : ℝ) (1 / (n + 1)) := by rw [← hψsupp n]; exact hu
        simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using h
      calc |H (t - u) - H t| ≤ M * |t - u - t| := hlip _ _
        _ = M * |u| := by rw [sub_sub_cancel_left, abs_neg]
        _ ≤ M * (1 / (n + 1)) := mul_le_mul_of_nonneg_left husupp.le hM

