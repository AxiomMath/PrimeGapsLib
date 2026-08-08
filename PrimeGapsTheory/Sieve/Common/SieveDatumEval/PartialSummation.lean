/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SieveDatumEval.Lipschitz

/-!
# Partial summation against a smooth weight

Compares the weighted partial sum with its integral, both for a smooth weight and in the sharp
form, via the Abel discrepancy.

## Main results

* `S1_partial_sum_sharp`
-/

@[expose] public section

open scoped Finset Topology
open MeasureTheory

namespace PrimeGaps


/-- **The Abel discrepancy is continuous under uniform convergence.**  If each `Hn n` is `C¹`,
`H` is continuous, and `|Hn n x - H x| ≤ M / (n + 1)` for all `x`, then both the weighted partial
sums and the integrals converge, hence so does the discrepancy
`|∑_{0 < d < z} S.h d · Hn n (log d / log z) - 𝔖 log z ∫₀¹ Hn n|`. -/
private theorem tendsto_abs_partialSum_sub_integral (S : SieveDatum) (z : ℝ) (M : ℝ)
    (H : ℝ → ℝ) (Hn : ℕ → ℝ → ℝ) (hHcont : Continuous H)
    (hHn_smooth : ∀ n, ContDiff ℝ 1 (Hn n))
    (hHn_conv : ∀ (n : ℕ) (x : ℝ), |Hn n x - H x| ≤ M * (1 / (n + 1))) :
    Filter.Tendsto (fun n ↦ |(∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
          S.h d * Hn n (Real.log ↑d / Real.log z)) -
        PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, Hn n x|)
      Filter.atTop
      (𝓝 |(∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
            S.h d * H (Real.log ↑d / Real.log z)) -
          PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, H x|) := by
  set SS := PrimeGaps.singularSeries S.γ
  set Sf : (ℝ → ℝ) → ℝ := fun F ↦ ∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
      S.h d * F (Real.log ↑d / Real.log z) with hSf
  set If : (ℝ → ℝ) → ℝ := fun F ↦ SS * Real.log z * ∫ x in (0 : ℝ)..1, F x with hIf
  have hrate : Filter.Tendsto (fun n : ℕ ↦ M * (1 / (n + 1))) Filter.atTop (𝓝 0) := by
    simpa using tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (M : ℝ)
  have hptwise : ∀ c : ℝ, Filter.Tendsto (fun n ↦ Hn n c) Filter.atTop (𝓝 (H c)) := by
    intro c
    have hsq : Filter.Tendsto (fun n ↦ Hn n c - H c) Filter.atTop (𝓝 0) :=
      squeeze_zero_norm (fun n ↦ by simpa only [Real.norm_eq_abs] using hHn_conv n c) hrate
    simpa using hsq.add (tendsto_const_nhds (x := H c))
  have hSf_tend : Filter.Tendsto (fun n ↦ Sf (Hn n)) Filter.atTop (𝓝 (Sf H)) := by
    rw [hSf]
    refine tendsto_finsetSum _ fun d _ ↦ ?_
    simpa using (hptwise (Real.log ↑d / Real.log z)).const_mul (S.h d)
  have hInt_tend : Filter.Tendsto (fun n ↦ ∫ x in (0 : ℝ)..1, Hn n x)
      Filter.atTop (𝓝 (∫ x in (0 : ℝ)..1, H x)) := by
    have hbound : ∀ n, |(∫ x in (0 : ℝ)..1, Hn n x) - ∫ x in (0 : ℝ)..1, H x| ≤ M * (1 / (n +
      1)) := by
      intro n
      have hii1 : IntervalIntegrable (Hn n) MeasureTheory.volume 0 1 :=
        (hHn_smooth n).continuous.intervalIntegrable 0 1
      have hii2 : IntervalIntegrable H MeasureTheory.volume 0 1 := hHcont.intervalIntegrable 0 1
      rw [← intervalIntegral.integral_sub hii1 hii2]
      calc |∫ x in (0 : ℝ)..1, (Hn n x - H x)| ≤ ∫ x in (0 : ℝ)..1, |Hn n x - H x| :=
            intervalIntegral.abs_integral_le_integral_abs (by norm_num)
        _ ≤ ∫ x in (0 : ℝ)..1, M * (1 / (n + 1)) :=
            intervalIntegral.integral_mono_on (by norm_num) (hii1.sub hii2).abs
              intervalIntegrable_const fun x _ ↦ hHn_conv n x
        _ = M * (1 / (n + 1)) := by simp
    have hsq : Filter.Tendsto (fun n ↦ (∫ x in (0 : ℝ)..1, Hn n x) - ∫ x in (0 : ℝ)..1, H x)
        Filter.atTop (𝓝 0) :=
      squeeze_zero_norm (fun n ↦ by simpa [Real.norm_eq_abs] using hbound n) hrate
    simpa using hsq.add (tendsto_const_nhds (x := ∫ x in (0 : ℝ)..1, H x))
  have hIf_tend : Filter.Tendsto (fun n ↦ If (Hn n)) Filter.atTop (𝓝 (If H)) := by
    rw [hIf]
    simpa [mul_assoc] using hInt_tend.const_mul (SS * Real.log z)
  exact (hSf_tend.sub hIf_tend).abs

/-- **Reduction to smooth test functions.**  A bound `RHS` for the Abel discrepancy that holds
for every `C¹` function `F` with `Gmax F ≤ 2 * M` also holds for an arbitrary `G` that is
bounded by `M` and `M`-Lipschitz on `[0, 1]`: clamp `G` to `[0, 1]`, approximate the clamped
function by the mollified family of `lip_smooth_approx`, and pass to the limit. -/
private theorem abs_partialSum_sub_integral_le_of_smooth (S : SieveDatum) (G : ℝ → ℝ) (M : ℝ)
    (hM : 0 ≤ M) (hbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ M)
    (hlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ M * |x - y|)
    (z : ℝ) (hz : 2 ≤ z) (RHS : ℝ)
    (hsmooth : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → Gmax F ≤ 2 * M →
      |∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z, S.h d * F (Real.log ↑d /
        Real.log z) -
        PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, F x| ≤ RHS) :
    |∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z, S.h d * G (Real.log ↑d / Real.log z) -
      PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, G x| ≤ RHS := by
  set p : ℝ → ℝ := fun t ↦ min 1 (max 0 t) with hp
  have hp_mem : ∀ t, p t ∈ Set.Icc (0 : ℝ) 1 := fun t ↦ by
    simp only [hp, Set.mem_Icc]
    exact ⟨le_min (by norm_num) (le_max_left _ _), min_le_left _ _⟩
  have hp_id : ∀ x ∈ Set.Icc (0 : ℝ) 1, p x = x := by
    intro x hx; simp only [hp]; rw [max_eq_right hx.1, min_eq_right hx.2]
  have hp_lip : ∀ s t, |p s - p t| ≤ |s - t| := by
    have hmax : LipschitzWith 1 (fun t : ℝ ↦ max 0 t) := by
      simpa using (LipschitzWith.const (0 : ℝ)).max (LipschitzWith.id)
    have hmin : LipschitzWith 1 (fun t : ℝ ↦ min 1 t) := by
      simpa using (LipschitzWith.const (1 : ℝ)).min (LipschitzWith.id)
    have h1 : LipschitzWith 1 (fun t : ℝ ↦ min 1 (max 0 t)) := by
      simpa [Function.comp_def] using hmin.comp hmax
    intro s t
    simpa [hp, Real.dist_eq] using h1.dist_le_mul s t
  set H : ℝ → ℝ := fun t ↦ G (p t) with hH
  have hH_bdd : ∀ t, |H t| ≤ M := fun t ↦ hbdd (p t) (hp_mem t)
  have hH_lip : ∀ s t, |H s - H t| ≤ M * |s - t| := fun s t ↦
    (hlip (p s) (hp_mem s) (p t) (hp_mem t)).trans (mul_le_mul_of_nonneg_left (hp_lip s t) hM)
  obtain ⟨Hn, hHn_smooth, hHn_gmax, hHn_conv⟩ := lip_smooth_approx H M hM hH_bdd hH_lip
  set SS := PrimeGaps.singularSeries S.γ
  set Sf : (ℝ → ℝ) → ℝ := fun F ↦ ∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
      S.h d * F (Real.log ↑d / Real.log z) with hSf
  set If : (ℝ → ℝ) → ℝ := fun F ↦ SS * Real.log z * ∫ x in (0 : ℝ)..1, F x with hIf
  have hstep_eq : |Sf G - If G| = |Sf H - If H| := by
    have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith)
    have hSfeq : Sf G = Sf H := by
      rw [hSf]
      refine Finset.sum_congr rfl fun d hd ↦ ?_
      simp only [Finset.mem_filter, Finset.mem_range] at hd
      obtain ⟨-, hdpos, hdz⟩ := hd
      have harg_mem : Real.log ↑d / Real.log z ∈ Set.Icc (0 : ℝ) 1 :=
        ⟨div_nonneg (Real.log_nonneg (by exact_mod_cast hdpos)) hlogz_pos.le,
          (div_le_one hlogz_pos).mpr (Real.log_le_log (by exact_mod_cast hdpos) hdz.le)⟩
      rw [hH]; simp only; rw [hp_id _ harg_mem]
    have hIntEq : (∫ x in (0 : ℝ)..1, G x) = ∫ x in (0 : ℝ)..1, H x := by
      refine intervalIntegral.integral_congr fun x hx ↦ ?_
      rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hx
      rw [hH]; simp only; rw [hp_id _ hx]
    have hIfeq : If G = If H := by
      rw [hIf]; simp only; rw [hIntEq]
    rw [hSfeq, hIfeq]
  have hHcont : Continuous H :=
    LipschitzWith.continuous (K := Real.toNNReal M) <| .of_dist_le_mul fun s t ↦ by
      rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal M hM]; exact hH_lip s t
  have hstep_limit : Filter.Tendsto (fun n ↦ |Sf (Hn n) - If (Hn n)|)
        Filter.atTop (𝓝 (|Sf H - If H|)) :=
    tendsto_abs_partialSum_sub_integral S z M H Hn hHcont hHn_smooth hHn_conv
  rw [hstep_eq]
  exact le_of_tendsto' hstep_limit fun n ↦ hsmooth (Hn n) (hHn_smooth n) (hHn_gmax n)

/-- Partial-summation bound comparing `∑_{0 < d < z} S.h d * G (log d / log z)` with
`𝔖 S.γ * log z * ∫₀¹ G`, for `G` bounded by `M` and `M`-Lipschitz on `[0,1]`. -/
theorem S1_partial_sum_lipschitz : ∃ (C₁ : ℝ → ℝ → ℝ → ℝ) (C₂ : ℝ → ℝ → ℝ),
      (∀ A₁ A₂ A₃ : ℝ, 0 < C₁ A₁ A₂ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < C₂ A₁ A₃) ∧
      ∀ (S : SieveDatum) (G : ℝ → ℝ) (M : ℝ), 0 ≤ M → (∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ M) →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ M * |x - y|) →
        ∀ z : ℝ, 2 ≤ z →
          |∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
              S.h d * G (Real.log ↑d / Real.log z) -
            PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, G x| ≤
          C₁ S.A₁ S.A₂ S.A₃ * PrimeGaps.singularSeries S.γ * S.L * (2 * M) +
            C₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                Real.log (2 * ↑S.V * z) / Real.log z * (2 * M) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hpart⟩ := lem_partial_sum
  refine ⟨C₁, C₂, hC₁, hC₂, ?_⟩
  intro S G M hM hbdd hlip z hz
  refine abs_partialSum_sub_integral_le_of_smooth S G M hM hbdd hlip z hz _ ?_
  intro F hF hFgmax
  refine le_trans (hpart S F hF z hz) ?_
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast S.V_pos
  have hlog2Vz_nonneg : 0 ≤ Real.log (2 * ↑S.V * z) := Real.log_nonneg (by
    linarith only [one_le_mul_of_one_le_of_one_le hV1 (by linarith only [hz] : (1 : ℝ) ≤ z)])
  have hcoeff1 : 0 ≤ C₁ S.A₁ S.A₂ S.A₃ * PrimeGaps.singularSeries S.γ * S.L :=
    mul_nonneg (mul_nonneg (hC₁ S.A₁ S.A₂ S.A₃).le (PrimeGaps.singularSeries_pos S).le) S.L_nonneg
  have hcoeff2 : 0 ≤ C₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
      Real.log (2 * ↑S.V * z) / Real.log z :=
    div_nonneg (mul_nonneg (mul_nonneg (hC₂ S.A₁ S.A₃).le (by positivity)) hlog2Vz_nonneg)
      (Real.log_pos (by linarith)).le
  exact add_le_add (mul_le_mul_of_nonneg_left hFgmax hcoeff1)
    (mul_le_mul_of_nonneg_left hFgmax hcoeff2)

/-- The τ-carrying part of the Abel integral tail has its `log(2Vt)` factor kept *inside* the
integral, so the weight `t^{-9/8}` concentrates its mass near `t=1`:
`∫₁^z t^{-9/8} log(2Vt) dt ≤ ∫₁^∞ t^{-9/8} log(2Vt) dt = 8 log(2V) + 64`.
-/
theorem S1sh_rpowint (z : ℝ) (hz : 2 ≤ z) : (∫ t in (1 : ℝ)..z, t ^ (-(9 : ℝ) / 8)) ≤ 8 := by
  have hz1 : (1 : ℝ) ≤ z := by linarith
  rw [integral_rpow (Or.inr ⟨by norm_num, by
      simp only [Set.uIcc_of_le hz1, Set.mem_Icc]; push Not; intro h; linarith⟩),
    show (-(9 : ℝ) / 8 + 1) = -(1 : ℝ) / 8 by ring, Real.one_rpow,
    div_le_iff_of_neg (by norm_num)]
  linarith only [Real.rpow_pos_of_pos (show (0 : ℝ) < z by linarith) (-(1 : ℝ) / 8),
    Real.rpow_le_one_of_one_le_of_nonpos hz1 (by norm_num : -(1 : ℝ) / 8 ≤ 0)]

/-- `t ↦ -8 * t^(-1/8) * (log t + 8)` is an antiderivative of `t ↦ t^(-9/8) * log t` on `t > 0`. -/
theorem S1sh_antideriv (t : ℝ) (ht : 0 < t) :
    HasDerivAt (fun t ↦ -8 * t ^ (-(1 : ℝ) / 8) * (Real.log t + 8))
      (t ^ (-(9 : ℝ) / 8) * Real.log t) t := by
  have hstep : t ^ (-(1 : ℝ) / 8) * (1 / t) = t ^ (-(9 : ℝ) / 8) := by
    rw [one_div, ← Real.rpow_neg_one t, ← Real.rpow_add ht]; norm_num
  have hprod := ((Real.hasDerivAt_rpow_const (p := -(1 : ℝ) / 8) (Or.inl ht.ne')).const_mul
      (-8 : ℝ)).mul
    (show HasDerivAt (fun t : ℝ ↦ Real.log t + 8) (1 / t) t by
      simpa using (Real.hasDerivAt_log ht.ne').add_const 8)
  have hval : -8 * (-(1 : ℝ) / 8 * t ^ (-(1 : ℝ) / 8 - 1)) * (Real.log t + 8) +
      -8 * t ^ (-(1 : ℝ) / 8) * (1 / t) = t ^ (-(9 : ℝ) / 8) * Real.log t := by
    rw [show (-(1 : ℝ) / 8 - 1) = -(9 : ℝ) / 8 by ring]
    linear_combination (-8 : ℝ) * hstep
  rwa [hval] at hprod

section
open scoped Interval

/-- `t ↦ 1 / t` is continuous on `uIcc a b` whenever `0 < a ≤ b`. -/
private theorem continuousOn_one_div_uIcc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ ↦ 1 / t) [[a, b]] := by
  apply ContinuousOn.div continuousOn_const continuousOn_id
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  simp only [Set.mem_Icc] at hx
  intro h; simp only [id] at h; linarith [hx.1, ha]

end

/-- `t ↦ c * (1 / t)` is interval integrable on `[a, b]` whenever `0 < a ≤ b`. -/
private theorem intervalIntegrable_const_mul_one_div (c : ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ ↦ c * (1 / t)) volume a b :=
  ((continuousOn_one_div_uIcc ha hab).intervalIntegrable).const_mul c

section
open scoped Interval

/-- `t ↦ t^(-9/8) * log (2 V t)` is continuous on `uIcc a b` whenever `1 ≤ V` and `0 < a ≤ b`. -/
private theorem continuousOn_rpow_mul_log_uIcc {V : ℝ} (hV : 1 ≤ V) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) :
    ContinuousOn (fun t : ℝ ↦ t ^ (-(9 : ℝ) / 8) * Real.log (2 * V * t)) [[a, b]] := by
  apply ContinuousOn.mul
  · apply ContinuousOn.rpow_const continuousOn_id
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    simp only [Set.mem_Icc] at hx
    left; simp only [id]; linarith only [hx.1, ha]
  · apply ContinuousOn.log
    · exact ContinuousOn.mul continuousOn_const continuousOn_id
    · intro x hx
      rw [Set.uIcc_of_le hab] at hx
      simp only [Set.mem_Icc] at hx
      exact ne_of_gt (mul_pos (by linarith only [hV]) (by linarith only [hx.1, ha]))

end

section
open scoped Interval

/-- Continuity of `t ↦ t^(-9/8)` on `uIcc 1 z`. -/
theorem S1sh_cont_rpow (z : ℝ) (hz : 2 ≤ z) :
    ContinuousOn (fun t : ℝ ↦ t ^ (-(9 : ℝ) / 8)) [[1, z]] := by
  have hz1 : (1 : ℝ) ≤ z := by linarith
  apply ContinuousOn.rpow_const continuousOn_id
  intro x hx; left
  rw [Set.uIcc_of_le hz1] at hx
  exact ne_of_gt (by simp at hx ⊢; linarith only [hx.1])

end

section
open scoped Interval

/-- Continuity of `t ↦ t^(-9/8) * log t` on `uIcc 1 z`. -/
theorem S1sh_cont_rpow_log (z : ℝ) (hz : 2 ≤ z) :
    ContinuousOn (fun t : ℝ ↦ t ^ (-(9 : ℝ) / 8) * Real.log t) [[1, z]] := by
  have hz1 : (1 : ℝ) ≤ z := by linarith
  apply ContinuousOn.mul (S1sh_cont_rpow z hz)
  apply ContinuousOn.log continuousOn_id
  intro x hx
  rw [Set.uIcc_of_le hz1] at hx
  simp at hx ⊢; linarith only [hx.1]

end

/-- `∫₁^z t^(-9/8) * log t ≤ 64`, uniformly in `z ≥ 2`. -/
theorem S1sh_logint (z : ℝ) (hz : 2 ≤ z) :
    (∫ t in (1 : ℝ)..z, t ^ (-(9 : ℝ) / 8) * Real.log t) ≤ 64 := by
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have heq : (∫ t in (1 : ℝ)..z, t ^ (-(9 : ℝ) / 8) * Real.log t) =
      (fun t ↦ -8 * t ^ (-(1 : ℝ) / 8) * (Real.log t + 8)) z -
        (fun t ↦ -8 * t ^ (-(1 : ℝ) / 8) * (Real.log t + 8)) 1 := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    · intro x hx
      rw [Set.uIcc_of_le hz1] at hx
      exact S1sh_antideriv x (by simp at hx; linarith only [hx.1])
    · exact (S1sh_cont_rpow_log z hz).intervalIntegrable
  rw [heq]
  simp only [Real.one_rpow, Real.log_one]
  linarith only [mul_nonneg (Real.rpow_pos_of_pos (show (0 : ℝ) < z by linarith) (-(1 : ℝ) / 8)).le
    (by linarith only [Real.log_nonneg hz1] : (0 : ℝ) ≤ Real.log z + 8)]

section
open scoped Interval

/-- `∫₁^z t^(-9/8) * log (2 V t) ≤ 8 * log (2 V) + 64`, uniformly in `z ≥ 2`. -/
theorem S1_sharp_integral_bound (V : ℕ) (hV : 0 < V) (z : ℝ) (hz : 2 ≤ z) :
    (∫ t in (1 : ℝ)..z, t ^ (-(9 : ℝ) / 8) * Real.log (2 * (V : ℝ) * t)) ≤
      8 * Real.log (2 * (V : ℝ)) + 64 := by
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hV1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hlog2V_nonneg : 0 ≤ Real.log (2 * (V : ℝ)) := Real.log_nonneg (by linarith)
  have hpoint : Set.EqOn (fun t : ℝ ↦ t ^ (-(9 : ℝ) / 8) * Real.log (2 * (V : ℝ) * t))
      (fun t : ℝ ↦ Real.log (2 * (V : ℝ)) * t ^ (-(9 : ℝ) / 8) + t ^ (-(9 : ℝ) / 8) * Real.log t)
      [[1, z]] := by
    intro x hx
    rw [Set.uIcc_of_le hz1] at hx
    simp only [Set.mem_Icc] at hx
    have hx0 : (0 : ℝ) < x := by linarith only [hx.1]
    have : Real.log (2 * (V : ℝ) * x) = Real.log (2 * (V : ℝ)) + Real.log x := by
      rw [Real.log_mul (by positivity) hx0.ne']
    simp only [this]; ring
  rw [intervalIntegral.integral_congr hpoint]
  have hint_rpow : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(9 : ℝ) / 8)) MeasureTheory.volume 1 z :=
    (S1sh_cont_rpow z hz).intervalIntegrable
  have hint_rpowlog : IntervalIntegrable (fun t : ℝ ↦ t ^ (-(9 : ℝ) / 8) * Real.log t)
      MeasureTheory.volume 1 z :=
    (S1sh_cont_rpow_log z hz).intervalIntegrable
  rw [intervalIntegral.integral_add (hint_rpow.const_mul _) hint_rpowlog,
      intervalIntegral.integral_const_mul]
  linarith only [mul_le_mul_of_nonneg_left (S1sh_rpowint z hz) hlog2V_nonneg, S1sh_logint z hz]

end

/-- `∫₂^z t^(-9/8) * log (2 V t) ≤ 8 * log (2 V) + 64`, uniformly in `z ≥ 2`: the integrand is
nonnegative throughout, so the integral over `[2, z]` is at most the one `S1_sharp_integral_bound`
bounds over `[1, z]`. -/
private theorem S1_sharp_integral_bound_two_z (V : ℕ) (hV : 0 < V) (z : ℝ) (hz : 2 ≤ z) :
    (∫ t in (2 : ℝ)..z, t ^ (-(9 : ℝ) / 8) * Real.log (2 * (V : ℝ) * t)) ≤
      8 * Real.log (2 * (V : ℝ)) + 64 := by
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hV1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (1 : ℝ) z)]
      fun t : ℝ ↦ t ^ (-(9 : ℝ) / 8) * Real.log (2 * (V : ℝ) * t) :=
    (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr
      (Filter.Eventually.of_forall fun t ht ↦
        mul_nonneg (Real.rpow_pos_of_pos (by linarith only [ht.1]) _).le
          (Real.log_nonneg (one_le_mul_of_one_le_of_one_le (by linarith only [hV1])
            (by linarith only [ht.1]))))
  exact le_trans (intervalIntegral.integral_mono_interval (by norm_num) hz le_rfl hnn
      (continuousOn_rpow_mul_log_uIcc hV1 one_pos hz1).intervalIntegrable)
    (S1_sharp_integral_bound V hV z hz)

/-- `S.H t = 1` for `1 < t < 2`, only `d = 1` contributing to the divisor sum. -/
theorem S1_H_eq_one (S : SieveDatum) (t : ℝ) (h1 : 1 < t) (h2 : t < 2) : S.H t = 1 := by
  rw [S.H_eq_sum_coprime, Finset.sum_eq_single 1]
  · rw [S.h_squarefree_eq_prod 1 (by simp)]; simp
  · intro b hb hb1
    simp only [Finset.mem_filter, Finset.mem_range] at hb
    obtain ⟨-, hpos, hbt, -⟩ := hb
    exfalso
    have : b < 2 := by exact_mod_cast hbt.trans h2
    omega
  · intro hnot
    exfalso
    apply hnot
    simp only [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Nat.lt_ceil.mpr (by exact_mod_cast h1)
    · norm_num
    · simpa using (by linarith : (1 : ℝ) < t)
    · simp [Nat.Coprime]

/-- The Abel integrand `t ↦ |S.H t - 𝔖 S.γ * log t| / t` is interval integrable on `[1, z]`. -/
theorem integrand_ii (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z) :
    IntervalIntegrable (fun t ↦ |S.H t - 𝔖 S.γ * Real.log t| / t) volume 1 z := by
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hlog := PrimeGaps.intervalIntegrable_const_mul_log (𝔖 S.γ) hz1
  rw [show (fun t ↦ |S.H t - 𝔖 S.γ * Real.log t| / t) =
      (fun t ↦ |S.H t - 𝔖 S.γ * Real.log t| * (1 / t)) by funext t; ring]
  exact (((PrimeGaps.intervalIntegrable_H S hz1).sub hlog).abs).mul_continuousOn
    (continuousOn_one_div_uIcc one_pos hz1)

/-- On `[1, 2]` the Abel integrand `|S.H t - 𝔖 log t| / t` is at most `(1 + 𝔖 log 2) / t`,
so `∫₁² |S.H t - 𝔖 log t| / t ≤ log 2 + 𝔖 (log 2) ^ 2`. -/
private theorem S1_intTail_one_two_le (S : SieveDatum) :
    (∫ t in (1 : ℝ)..2, |S.H t - 𝔖 S.γ * Real.log t| / t) ≤
      Real.log 2 + 𝔖 S.γ * (Real.log 2) ^ 2 := by
  set SS := 𝔖 S.γ with hSS
  have hSS_pos : 0 < SS := by rw [hSS]; exact PrimeGaps.singularSeries_pos S
  have hii12 : IntervalIntegrable (fun t ↦ |S.H t - SS * Real.log t| / t) volume 1 2 := by
    have := integrand_ii S 2 le_rfl; rwa [hSS]
  have hbound : ∀ t ∈ Set.Icc (1 : ℝ) 2, |S.H t - SS * Real.log t| / t ≤
      (1 + SS * Real.log 2) * (1 / t) := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0 : ℝ) < t := by linarith only [ht.1]
    obtain ⟨hH1, hH2⟩ := abs_le.mp (H_abs_le_one_on_Icc12 S t ht.2)
    have hlogt : 0 ≤ Real.log t := Real.log_nonneg (by linarith only [ht.1])
    have hlogt2 : Real.log t ≤ Real.log 2 := Real.log_le_log htpos ht.2
    have hnum : |S.H t - SS * Real.log t| ≤ 1 + SS * Real.log 2 := by
      rw [abs_le]
      constructor <;> linarith only [hH1, hH2, mul_nonneg hSS_pos.le hlogt,
          mul_le_mul_of_nonneg_left hlogt2 hSS_pos.le]
    rw [div_eq_mul_inv, ← one_div]
    exact mul_le_mul_of_nonneg_right hnum (by positivity)
  calc (∫ t in (1 : ℝ)..2, |S.H t - SS * Real.log t| / t)
      ≤ ∫ t in (1 : ℝ)..2, (1 + SS * Real.log 2) * (1 / t) := by
        refine intervalIntegral.integral_mono_on (by norm_num) hii12 ?_ hbound
        exact intervalIntegrable_const_mul_one_div _ one_pos (by norm_num)
    _ = (1 + SS * Real.log 2) * ∫ t in (1 : ℝ)..2, (1 / t) := by
        rw [intervalIntegral.integral_const_mul]
    _ = (1 + SS * Real.log 2) * Real.log 2 := by
        rw [integral_one_div (by
          rw [Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
          simp only [Set.mem_Icc]; norm_num)]
        norm_num
    _ = Real.log 2 + SS * (Real.log 2) ^ 2 := by ring

/-- On `[2, z]` the pointwise asymptotic for `S.H` majorises the Abel integrand by
`A / t + B * t ^ (-9/8) * log (2 V t)`; integrating and applying `S1_sharp_integral_bound`
gives `∫₂ᶻ |S.H t - 𝔖 log t| / t ≤ A * log z + B * (8 * log (2 V) + 64)`, where
`A = C₁ * 𝔖 * (1 + ellV V)` and `B = C₂ * τ V`. -/
private theorem S1_intTail_two_z_le (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z)
    (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hHasymp : ∀ (t : ℝ), 2 ≤ t →
      |S.H t - 𝔖 S.γ * Real.log t| ≤ C₁ * 𝔖 S.γ * (1 + ellV S.V) +
          C₂ * ↑(#S.V.divisors) * t ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) :
    (∫ t in (2 : ℝ)..z, |S.H t - 𝔖 S.γ * Real.log t| / t) ≤ C₁ * 𝔖 S.γ * (1 + ellV S.V) *
      Real.log z +
        C₂ * (#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) := by
  set SS := 𝔖 S.γ with hSS
  have hSS_pos : 0 < SS := by rw [hSS]; exact PrimeGaps.singularSeries_pos S
  have hVpos : 0 < S.V := S.V_pos
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast hVpos
  have hcard_nonneg : (0 : ℝ) ≤ (#S.V.divisors : ℝ) := by positivity
  have hpLSL_nonneg : (0 : ℝ) ≤ ellV S.V := ellV_nonneg S.V
  have hii2z : IntervalIntegrable (fun t ↦ |S.H t - SS * Real.log t| / t) volume 2 z := by
    rw [hSS]
    exact (integrand_ii S z hz).mono_set (by
      rw [Set.uIcc_of_le hz, Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ z)]
      exact Set.Icc_subset_Icc (by norm_num) le_rfl)
  set A := C₁ * SS * (1 + ellV S.V) with hA
  set B := C₂ * (#S.V.divisors : ℝ) with hB
  have hA_nonneg : 0 ≤ A := by rw [hA]; positivity
  have hB_nonneg : 0 ≤ B := by rw [hB]; positivity
  set g : ℝ → ℝ := fun t ↦ A * (1 / t) + B * (t ^ (-(9 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) with hg
  have hg1_ii : IntervalIntegrable (fun t ↦ A * (1 / t)) volume 2 z :=
    intervalIntegrable_const_mul_one_div A two_pos hz
  have hg2_ii : IntervalIntegrable (fun t ↦ B * (t ^ (-(9 : ℝ) / 8) * Real.log (2 * ↑S.V * t)))
      volume 2 z :=
    ((continuousOn_rpow_mul_log_uIcc hV1 two_pos hz).intervalIntegrable).const_mul B
  have hg_ii : IntervalIntegrable g volume 2 z := by rw [hg]; exact hg1_ii.add hg2_ii
  have hpoint : ∀ t ∈ Set.Icc (2 : ℝ) z, |S.H t - SS * Real.log t| / t ≤ g t := by
    intro t ht
    simp only [Set.mem_Icc] at ht
    have htpos : (0 : ℝ) < t := by linarith only [ht.1]
    rw [hg]; simp only
    have hrpow : t ^ (-(9 : ℝ) / 8) * t = t ^ (-(1 : ℝ) / 8) := by
      nth_rewrite 2 [← Real.rpow_one t]
      rw [← Real.rpow_add htpos]; norm_num
    rw [div_le_iff₀ htpos, show (A * (1 / t) +
        B * (t ^ (-(9 : ℝ) / 8) * Real.log (2 * ↑S.V * t))) * t =
          A + B * t ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * t) by
      rw [add_mul, mul_assoc A, one_div, inv_mul_cancel₀ htpos.ne', mul_one]
      congr 1
      rw [mul_assoc B, mul_assoc B, mul_comm (t ^ (-(9 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) t,
          ← mul_assoc t, mul_comm t (t ^ (-(9 : ℝ) / 8)), hrpow]]
    exact hHasymp t ht.1
  have hgsplit : (∫ t in (2 : ℝ)..z, g t) = A * (∫ t in (2 : ℝ)..z, (1 / t)) +
        B * (∫ t in (2 : ℝ)..z, t ^ (-(9 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) := by
    rw [hg, intervalIntegral.integral_add hg1_ii hg2_ii,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hint1 : (∫ t in (2 : ℝ)..z, (1 / t)) ≤ Real.log z := by
    rw [integral_one_div (by rw [Set.uIcc_of_le hz]; simp only [Set.mem_Icc]; norm_num),
      Real.log_div (by linarith : (0 : ℝ) < z).ne' (by norm_num)]
    linarith only [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  calc (∫ t in (2 : ℝ)..z, |S.H t - SS * Real.log t| / t)
      ≤ ∫ t in (2 : ℝ)..z, g t := intervalIntegral.integral_mono_on hz hii2z hg_ii hpoint
    _ = A * (∫ t in (2 : ℝ)..z, (1 / t)) +
        B * (∫ t in (2 : ℝ)..z, t ^ (-(9 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) := hgsplit
    _ ≤ A * Real.log z + B * (8 * Real.log (2 * ↑S.V) + 64) :=
        add_le_add (mul_le_mul_of_nonneg_left hint1 hA_nonneg)
          (mul_le_mul_of_nonneg_left (S1_sharp_integral_bound_two_z S.V hVpos z hz) hB_nonneg)

/-- Bound for the Abel tail `∫₁^z |S.H t - 𝔖 S.γ * log t| / t`, obtained from the pointwise
asymptotic for `S.H` and the sharp integral bound `S1_sharp_integral_bound`. -/
theorem S1_intTail_bound (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z)
    (C₁ C₂ : ℝ) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂)
    (hHasymp : ∀ (t : ℝ), 2 ≤ t →
      |S.H t - 𝔖 S.γ * Real.log t| ≤ C₁ * 𝔖 S.γ * (1 + ellV S.V) +
          C₂ * ↑(#S.V.divisors) * t ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) :
    (∫ t in (1 : ℝ)..z, |S.H t - 𝔖 S.γ * Real.log t| / t) ≤ C₁ * 𝔖 S.γ * (1 + ellV S.V) *
      Real.log z + C₂ * (#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) +
        (Real.log 2 + 𝔖 S.γ * (Real.log 2) ^ 2) := by
  have hii12 : IntervalIntegrable (fun t ↦ |S.H t - 𝔖 S.γ * Real.log t| / t) volume 1 2 :=
    integrand_ii S 2 le_rfl
  have hii2z : IntervalIntegrable (fun t ↦ |S.H t - 𝔖 S.γ * Real.log t| / t) volume 2 z :=
    (integrand_ii S z hz).mono_set (by
      rw [Set.uIcc_of_le hz, Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ z)]
      exact Set.Icc_subset_Icc (by norm_num) le_rfl)
  rw [← intervalIntegral.integral_add_adjacent_intervals hii12 hii2z]
  linarith only [S1_intTail_one_two_le S, S1_intTail_two_z_le S z hz C₁ C₂ hC₁ hC₂ hHasymp]

/-- **The Abel bracket bound.**  The endpoint term plus the normalised Abel tail,
`|S.H z - 𝔖 log z| + (1 / log z) ∫₁^z |S.H t - 𝔖 log t| / t`, is at most
`2 (c₁ + 1) 𝔖 (1 + ellV V) + (c₂ + 1) τ V (z^(-1/8) log (2 V z) + (8 log (2 V) + 64) / log z)`.
Both the `log 2` and the `𝔖 (log 2)²` leftovers of `S1_intTail_bound` are absorbed by the `+ 1`
slack in the two constants. -/
private theorem abel_bracket_le (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hHasymp : ∀ t : ℝ, 2 ≤ t →
      |S.H t - 𝔖 S.γ * Real.log t| ≤ c₁ * 𝔖 S.γ * (1 + ellV S.V) +
          c₂ * ↑(#S.V.divisors) * t ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) :
    |S.H z - 𝔖 S.γ * Real.log z| +
        1 / Real.log z * ∫ (t : ℝ) in 1..z, |S.H t - 𝔖 S.γ * Real.log t| / t ≤
      2 * (c₁ + 1) * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
        (c₂ + 1) * (#S.V.divisors : ℝ) * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z) +
          (8 * Real.log (2 * ↑S.V) + 64) / Real.log z) := by
  set SS := PrimeGaps.singularSeries S.γ with hSS
  have hSS_pos : 0 < SS := by rw [hSS]; exact PrimeGaps.singularSeries_pos S
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hVpos : 0 < S.V := S.V_pos
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast hVpos
  have hcard_nonneg : (0 : ℝ) ≤ (#S.V.divisors : ℝ) := by positivity
  have hpLSL_nonneg : (0 : ℝ) ≤ ellV S.V := ellV_nonneg S.V
  have hzpow_nonneg : (0 : ℝ) ≤ z ^ (-(1 : ℝ) / 8) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hlog2Vz_nonneg : 0 ≤ Real.log (2 * ↑S.V * z) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (by linarith only [hV1]) (by linarith only [hz]))
  have hlog2V_nonneg : 0 ≤ Real.log (2 * ↑S.V) := Real.log_nonneg (by linarith only [hV1])
  have hEnd' : |S.H z - 𝔖 S.γ * Real.log z| ≤ c₁ * SS * (1 + ellV S.V) +
        c₂ * (#S.V.divisors : ℝ) * z ^ (-(1 : ℝ) / 8) *
            Real.log (2 * ↑S.V * z) := by
    rw [hSS]; convert hHasymp z hz using 3
  have hIntTail' : (1 / Real.log z) * ∫ (t : ℝ) in 1..z, |S.H t - 𝔖 S.γ * Real.log t| / t ≤
      c₁ * SS * (1 + ellV S.V) +
        c₂ * (#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) / Real.log z +
        (Real.log 2 + SS * (Real.log 2) ^ 2) / Real.log z := by
    have hIT : (∫ t in (1 : ℝ)..z, |S.H t - 𝔖 S.γ * Real.log t| / t) ≤
        c₁ * SS * (1 + ellV S.V) * Real.log z +
          c₂ * (#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) +
          (Real.log 2 + SS * (Real.log 2) ^ 2) := by
      rw [hSS]
      exact S1_intTail_bound S z hz c₁ c₂ hc₁ hc₂ hHasymp
    exact (mul_le_mul_of_nonneg_left hIT (by positivity)).trans_eq (by field_simp)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2_lt1 : Real.log 2 < 1 := by
    linarith [Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)]
  have hcard1 : (1 : ℝ) ≤ (#S.V.divisors : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hVpos.ne'⟩
  have hsq_bound : SS * (Real.log 2) ^ 2 / Real.log z ≤ 2 * SS * (1 + ellV S.V) := by
    have h1 : (Real.log 2) ^ 2 / Real.log z ≤ Real.log 2 := by
      rw [div_le_iff₀ hlogz_pos, pow_two]
      exact mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num) (by linarith)) hlog2_pos.le
    rw [mul_div_assoc]
    calc SS * ((Real.log 2) ^ 2 / Real.log z) ≤ SS * Real.log 2 :=
          mul_le_mul_of_nonneg_left h1 hSS_pos.le
      _ ≤ SS * (2 * (1 + ellV S.V)) := mul_le_mul_of_nonneg_left
            (by linarith only [hlog2_lt1, hpLSL_nonneg]) hSS_pos.le
      _ = 2 * SS * (1 + ellV S.V) := by ring
  have hconst_bound : Real.log 2 / Real.log z ≤
      (#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) / Real.log z := by
    have h := mul_le_mul_of_nonneg_right hcard1
      (show (0 : ℝ) ≤ 8 * Real.log (2 * ↑S.V) + 64 by linarith only [hlog2V_nonneg])
    exact div_le_div_of_nonneg_right (by linarith only [hlog2_lt1, hlog2V_nonneg, h]) hlogz_pos.le
  have hP_nonneg : 0 ≤ (#S.V.divisors : ℝ) * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z)) :=
    mul_nonneg hcard_nonneg (mul_nonneg hzpow_nonneg hlog2Vz_nonneg)
  have hQ_nonneg : 0 ≤ (#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) / Real.log z :=
    div_nonneg (mul_nonneg hcard_nonneg
      (by linarith only [hlog2V_nonneg] : (0 : ℝ) ≤ 8 * Real.log (2 * ↑S.V) + 64)) hlogz_pos.le
  refine (add_le_add hEnd' hIntTail').trans ?_
  rw [show c₂ * (#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) / Real.log z =
        c₂ * ((#S.V.divisors : ℝ) * (8 * Real.log (2 * ↑S.V) + 64) / Real.log z) by ring,
    show (Real.log 2 + SS * (Real.log 2) ^ 2) / Real.log z =
        Real.log 2 / Real.log z + SS * (Real.log 2) ^ 2 / Real.log z from add_div _ _ _,
    show (c₂ + 1) * (#S.V.divisors : ℝ) * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z) +
            (8 * Real.log (2 * ↑S.V) + 64) / Real.log z) =
        (c₂ + 1) * ((#S.V.divisors : ℝ) * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z))) +
          (c₂ + 1) * ((#S.V.divisors : ℝ) *
            (8 * Real.log (2 * ↑S.V) + 64) / Real.log z) by ring]
  linarith only [hsq_bound, hconst_bound, hP_nonneg, hQ_nonneg]

/-- **Sharp Abel bound for one smooth test function.**  For `C¹` `F` with `Gmax F ≤ 2 * M`, the
Abel discrepancy of the weighted sieve sum against `𝔖 log z ∫₀¹ F` is at most
`2 M (2 (c₁ + 1) 𝔖 (1 + ellV V) + (c₂ + 1) τ V (z^(-1/8) log (2 V z) +
(8 log (2 V) + 64) / log z))`. -/
private theorem abs_partialSum_sub_integral_sharp_le (S : SieveDatum) (F : ℝ → ℝ)
    (hF : ContDiff ℝ 1 F) (M : ℝ) (hFgmax : Gmax F ≤ 2 * M) (z : ℝ) (hz : 2 ≤ z)
    (c₁ c₂ : ℝ) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hHasymp : ∀ t : ℝ, 2 ≤ t →
      |S.H t - 𝔖 S.γ * Real.log t| ≤ c₁ * 𝔖 S.γ * (1 + ellV S.V) +
          c₂ * ↑(#S.V.divisors) * t ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) :
    |∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z, S.h d * F (Real.log ↑d / Real.log z) -
      PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, F x| ≤
      (2 * M) * ( 2 * (c₁ + 1) * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
        (c₂ + 1) * (#S.V.divisors : ℝ) * ( z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z) +
          (8 * Real.log (2 * ↑S.V) + 64) / Real.log z ) ) := by
  set SS := PrimeGaps.singularSeries S.γ with hSS
  set RHS : ℝ := (2 * M) * ( 2 * (c₁ + 1) * SS * (1 + ellV S.V) +
        (c₂ + 1) * (#S.V.divisors : ℝ) * ( z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V *
          z) + (8 * Real.log (2 * ↑S.V) + 64) / Real.log z ) ) with hRHS
  have hSS_pos : 0 < SS := by rw [hSS]; exact PrimeGaps.singularSeries_pos S
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast S.V_pos
  have hGmax_nonneg : 0 ≤ Gmax F := le_trans (abs_nonneg _) ((Gmax_bounds F hF (t := (0 : ℝ))
      (by constructor <;> norm_num)).1)
  have hcard_nonneg : (0 : ℝ) ≤ (#S.V.divisors : ℝ) := by positivity
  rw [hSS]
  refine le_trans (partial_sum_abel S F hF z hz) ?_
  have hzpow_nonneg : (0 : ℝ) ≤ z ^ (-(1 : ℝ) / 8) := (Real.rpow_pos_of_pos (by linarith) _).le
  have hlog2Vz_nonneg : 0 ≤ Real.log (2 * ↑S.V * z) := Real.log_nonneg
    (one_le_mul_of_one_le_of_one_le (by linarith only [hV1]) (by linarith only [hz]))
  have hlog2V_nonneg : 0 ≤ Real.log (2 * ↑S.V) := Real.log_nonneg (by linarith only [hV1])
  set INN : ℝ := 2 * (c₁ + 1) * SS * (1 + ellV S.V) +
      (c₂ + 1) * (#S.V.divisors : ℝ) * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z) +
              (8 * Real.log (2 * ↑S.V) + 64) / Real.log z) with hINN
  have hINN_nonneg : 0 ≤ INN := by
    rw [hINN]
    exact add_nonneg
      (mul_nonneg (mul_nonneg (by linarith only [hc₁]) hSS_pos.le)
        (by linarith only [ellV_nonneg S.V]))
      (mul_nonneg (mul_nonneg (by linarith only [hc₂]) hcard_nonneg)
        (add_nonneg (mul_nonneg hzpow_nonneg hlog2Vz_nonneg)
          (div_nonneg (by linarith only [hlog2V_nonneg]) hlogz_pos.le)))
  have hbracket : |S.H z - 𝔖 S.γ * Real.log z| +
        1 / Real.log z * ∫ (t : ℝ) in 1..z, |S.H t - 𝔖 S.γ * Real.log t| / t ≤ INN := by
    rw [hINN, hSS]
    exact abel_bracket_le S z hz c₁ c₂ hc₁ hc₂ hHasymp
  calc Gmax F * (|S.H z - 𝔖 S.γ * Real.log z| +
          1 / Real.log z * ∫ (t : ℝ) in 1..z, |S.H t - 𝔖 S.γ * Real.log t| / t) ≤
        Gmax F * INN := mul_le_mul_of_nonneg_left hbracket hGmax_nonneg
    _ ≤ (2 * M) * INN := mul_le_mul_of_nonneg_right hFgmax hINN_nonneg
    _ = RHS := by rw [hRHS, hINN]

/-- Sharp form of `S1_partial_sum_lipschitz`: the divisor-count error carries the two small
factors `z^(-1/8) * log (2 V z)` and `(8 * log (2 V) + 64) / log z`. -/
theorem S1_partial_sum_sharp : ∃ (C₁ : ℝ → ℝ → ℝ) (C₂ : ℝ → ℝ → ℝ),
      (∀ A₁ A₃ : ℝ, 0 < C₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < C₂ A₁ A₃) ∧
      ∀ (S : SieveDatum) (G : ℝ → ℝ) (M : ℝ), 0 ≤ M → (∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ M) →
        (∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ M * |x - y|) →
        ∀ z : ℝ, 2 ≤ z →
          |∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
              S.h d * G (Real.log ↑d / Real.log z) -
            PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, G x| ≤ (2 * M) *
              ( 2 * C₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
                C₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                    ( z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z) +
                        (8 * Real.log (2 * ↑S.V) + 64) / Real.log z ) ) := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hHasymp⟩ := PrimeGaps.slem_H_error_assembly
  refine ⟨fun A₁ A₃ ↦ C₁ A₁ A₃ + 1, fun A₁ A₃ ↦ C₂ A₁ A₃ + 1,
    fun A₁ A₃ ↦ by linarith only [hC₁ A₁ A₃], fun A₁ A₃ ↦ by linarith only [hC₂ A₁ A₃], ?_⟩
  intro S G M hM hbdd hlip z hz
  set SS := PrimeGaps.singularSeries S.γ
  set Sf : (ℝ → ℝ) → ℝ := fun F ↦ ∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
      S.h d * F (Real.log ↑d / Real.log z)
  set If : (ℝ → ℝ) → ℝ := fun F ↦ SS * Real.log z * ∫ x in (0 : ℝ)..1, F x
  set RHS : ℝ := (2 * M) * ( 2 * (C₁ S.A₁ S.A₃ + 1) * SS * (1 + ellV S.V) +
        (C₂ S.A₁ S.A₃ + 1) * (#S.V.divisors : ℝ) * ( z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V *
          z) + (8 * Real.log (2 * ↑S.V) + 64) / Real.log z ) )
  have hstep_bound : ∀ F : ℝ → ℝ, ContDiff ℝ 1 F → Gmax F ≤ 2 * M → |Sf F - If F| ≤ RHS :=
    fun F hF hFgmax ↦ abs_partialSum_sub_integral_sharp_le S F hF M hFgmax z hz
      (C₁ S.A₁ S.A₃) (C₂ S.A₁ S.A₃) (hC₁ S.A₁ S.A₃) (hC₂ S.A₁ S.A₃)
      (fun t ht ↦ hHasymp S t ht)
  exact abs_partialSum_sub_integral_le_of_smooth S G M hM hbdd hlip z hz RHS hstep_bound

end PrimeGaps
