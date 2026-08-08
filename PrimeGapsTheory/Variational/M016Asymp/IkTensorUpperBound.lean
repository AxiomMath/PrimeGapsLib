/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.MeasureTheory.Integral.Pi
public import Mathlib.Topology.Separation.CompletelyRegular
public import PrimeGapsTheory.Variational.M016Asymp.MuClosedForm
public import PrimeGapsTheory.Variational.SmoothApprox

/-!
# Tensor-product upper bound for a simplex integral

A product integral over the standard simplex is bounded by the corresponding integral over a
product of half-lines, which equals a power of a one-dimensional integral.

## Main definitions

* `SimplexIntegralBound.g`: The weight `A0_GPositive.g` truncated to `[0, T]`.
* `SimplexIntegralBound.I`: The product integral of the squared weight over the simplex.

## Main results

* `SimplexIntegralBound.integral_Ioi_g_sq_eq_gamma`: The one-dimensional integral of the squared
  truncated weight is `A1_MuClosedForm.gamma`.
* `SimplexIntegralBound.simplex_integral_bound`: The tensor-product upper bound for `I`,
  in closed form.
-/

@[expose] public section

namespace PrimeGaps.M016Asymp.B1_IkTensorUpperBound

open MeasureTheory

namespace SimplexIntegralBound

/-- The reciprocal affine weight `A0_GPositive.g` truncated to $[0, T]$, extended by $0$
outside $[0, T]$. -/
@[nolint defsWithUnderscore]
noncomputable def g (A T : ℝ) (u : ℝ) : ℝ := Set.indicator (Set.Icc (0 : ℝ) T) (A0_GPositive.g A) u

/-- The multi-dimensional integral
$I_k = \int_{\mathcal{R}_k} \prod_{i=1}^k g(k\, t_i)^2 \, dt_1 \cdots dt_k$. -/
@[nolint defsWithUnderscore]
noncomputable def I (k : ℕ) (A T : ℝ) : ℝ :=
  ∫ t in PrimeGaps.simplexPi k 1, ∏ i, (g A T ((k : ℝ) * t i)) ^ 2

/-- Squaring commutes with the truncation: $g(u)^2 = \mathbf{1}_{[0,T]}(u)\, g_A(u)^2$. -/
lemma sq_g_eq_indicator (A T : ℝ) (u : ℝ) : (g A T u) ^ 2 =
    Set.indicator (Set.Icc (0 : ℝ) T) (fun v ↦ (A0_GPositive.g A v) ^ 2) u := by
  by_cases hu : u ∈ Set.Icc (0 : ℝ) T <;> simp [g, hu]

/-- Truncating to $[0, T]$ and integrating over $(0, \infty)$ is integrating over $(0, T)$, so the
integral of the squared truncated weight is the closed-form `A1_MuClosedForm.gamma`. -/
lemma integral_Ioi_g_sq_eq_gamma (A T : ℝ) (hT : 0 ≤ T) :
    (∫ u in Set.Ioi (0 : ℝ), (g A T u) ^ 2) = A1_MuClosedForm.gamma A T := by
  have hinter : Set.Ioi (0 : ℝ) ∩ Set.Icc (0 : ℝ) T = Set.Ioc (0 : ℝ) T := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Icc, Set.mem_Ioc]
    exact ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun h ↦ ⟨h.1, h.1.le, h.2⟩⟩
  unfold A1_MuClosedForm.gamma
  rw [intervalIntegral.integral_of_le hT]
  simp_rw [sq_g_eq_indicator]
  rw [MeasureTheory.setIntegral_indicator measurableSet_Icc, hinter]

/-- Change-of-variables identity on $(0,\infty)$: for $c > 0$,
$\int_{(0,\infty)} g(c t)^2\, dt = c^{-1} \int_{(0,\infty)} g(u)^2\, du$. -/
lemma integral_g_sq_mul_left (A T c : ℝ) (hc : 0 < c) :
    (∫ t in Set.Ioi (0 : ℝ), (g A T (c * t)) ^ 2) =
      c⁻¹ * ∫ u in Set.Ioi (0 : ℝ), (g A T u) ^ 2 := by
  simpa using MeasureTheory.integral_comp_mul_left_Ioi (fun u ↦ (g A T u) ^ 2) 0 hc

/-- The substitution $u = k t$ gives $\int_{(0,\infty)} g(kt)^2\, dt = \gamma / k$. -/
lemma integral_g_sq_kt (k : ℕ) (A T : ℝ) (hk : 2 ≤ k) (hT : 0 ≤ T) :
    ∫ t in Set.Ioi (0 : ℝ), (g A T ((k : ℝ) * t)) ^ 2 = A1_MuClosedForm.gamma A T / (k : ℝ) := by
  rw [integral_g_sq_mul_left A T (k : ℝ) (Nat.cast_pos.mpr (by omega)),
    integral_Ioi_g_sq_eq_gamma A T hT, div_eq_inv_mul]

/-- The product of the squared weights is nonnegative. -/
lemma prod_g_sq_nonneg (k : ℕ) (A T : ℝ) (t : Fin k → ℝ) : 0 ≤ ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 :=
  Finset.prod_nonneg (fun _ _ ↦ sq_nonneg _)

/-- The simplex is contained in $[0,\infty)^k$. -/
lemma simplex_subset_pi_Ici (k : ℕ) :
    PrimeGaps.simplexPi k 1 ⊆ Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ)) :=
  fun _ ht i _ ↦ ht.1 i

/-- For all $u$, the function `g A T u` is in $[0, 1]$. -/
lemma g_mem_unitInterval (A T : ℝ) (hA : 0 < A) (u : ℝ) : g A T u ∈ Set.Icc (0 : ℝ) 1 := by
  by_cases hu : u ∈ Set.Icc (0 : ℝ) T
  · have hval : g A T u = A0_GPositive.g A u := Set.indicator_of_mem hu _
    rw [hval]
    exact ⟨(A0_GPositive.g_pos A T hA u hu).le, A0_GPositive.g_le_one A T hA u hu⟩
  · simp [g, hu]

/-- The integrand is bounded above by $1$. -/
lemma prod_g_sq_le_one (k : ℕ) (A T : ℝ) (hA : 0 < A) (t : Fin k → ℝ) :
    ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 ≤ 1 := by
  refine Finset.prod_le_one (fun _ _ ↦ sq_nonneg _) (fun i _ ↦ ?_)
  obtain ⟨h0, h1⟩ := g_mem_unitInterval A T hA ((k : ℝ) * t i)
  exact pow_le_one₀ h0 h1

/-- The integrand has support contained in $[0, T/k]^k$. -/
lemma prod_g_sq_support_subset (k : ℕ) (A T : ℝ) (hk : 0 < k) :
    Function.support (fun t : Fin k → ℝ ↦ ∏ i, (g A T ((k : ℝ) * t i)) ^ 2) ⊆
      Set.univ.pi (fun _ : Fin k ↦ Set.Icc (0 : ℝ) (T / k)) := by
  intro t ht i _
  rw [Function.mem_support] at ht
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hg : g A T ((k : ℝ) * t i) ≠ 0 := fun h ↦
    ht (Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h]; ring))
  have hkt : (k : ℝ) * t i ∈ Set.Icc (0 : ℝ) T := by
    by_contra hne
    exact hg (Set.indicator_of_notMem hne _)
  refine ⟨(mul_nonneg_iff_of_pos_left hk').mp hkt.1, ?_⟩
  rw [le_div_iff₀ hk']
  linarith [hkt.2]

/-- Measurability of `g A T`. -/
lemma measurable_g (A T : ℝ) : Measurable (g A T) :=
  Measurable.indicator ((measurable_const.mul measurable_id').const_add 1 |>.const_div 1)
    measurableSet_Icc

/-- Measurability of the integrand. -/
lemma measurable_prod_g_sq (k : ℕ) (A T : ℝ) :
    Measurable (fun t : Fin k → ℝ ↦ ∏ i, (g A T ((k : ℝ) * t i)) ^ 2) := by
  refine Finset.measurable_prod _ fun i _ ↦ ?_
  have h1 : Measurable (fun t : Fin k → ℝ ↦ t i) := measurable_pi_apply i
  have h2 : Measurable (fun t : Fin k → ℝ ↦ (k : ℝ) * t i) := h1.const_mul (k : ℝ)
  exact ((measurable_g A T).comp h2).pow_const 2

/-- The box $[0, T/k]^k$ has finite Lebesgue measure. -/
lemma volume_pi_Icc_lt_top (k : ℕ) (T : ℝ) :
    volume (Set.univ.pi (fun _ : Fin k ↦ Set.Icc (0 : ℝ) (T / k))) < ⊤ :=
  IsCompact.measure_lt_top (isCompact_univ_pi (fun _ ↦ isCompact_Icc))

/-- A nonnegative bounded measurable function with support of finite measure is integrable. -/
lemma integrable_of_bounded_support_finite_measure
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {B : Set α}
    (hf_meas : Measurable f) (hf_nonneg : ∀ x, 0 ≤ f x) (hf_bound : ∀ x, f x ≤ 1)
    (hf_supp : Function.support f ⊆ B) (h_volB : μ B < ⊤) :
    Integrable f μ := by
  have h_supp_meas : MeasurableSet (Function.support f) :=
    hf_meas (MeasurableSet.compl (MeasurableSet.singleton 0))
  have h_supp_vol : μ (Function.support f) < ⊤ := lt_of_le_of_lt (measure_mono hf_supp) h_volB
  set dom : α → ℝ := (Function.support f).indicator (fun _ ↦ (1 : ℝ)) with hdom_def
  have hdom_int : Integrable dom μ := by
    rw [hdom_def, integrable_indicator_iff h_supp_meas]
    exact integrableOn_const h_supp_vol.ne
  refine hdom_int.mono' hf_meas.aestronglyMeasurable (Filter.Eventually.of_forall fun x ↦ ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (hf_nonneg x)]
  by_cases hx : x ∈ Function.support f
  · rw [hdom_def, Set.indicator_of_mem hx]
    exact hf_bound x
  · rw [hdom_def, Set.indicator_of_notMem hx, not_not.mp hx]

/-- The integrand is integrable on $[0,\infty)^k$. -/
lemma integrable_prod_g_sq_pi_Ici (k : ℕ) (A T : ℝ) (hk : 0 < k) (hA : 0 < A) :
    IntegrableOn (fun t : Fin k → ℝ ↦ ∏ i, (g A T ((k : ℝ) * t i)) ^ 2)
      (Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ))) volume :=
  (integrable_of_bounded_support_finite_measure (measurable_prod_g_sq k A T)
    (prod_g_sq_nonneg k A T)
    (prod_g_sq_le_one k A T hA)
    (prod_g_sq_support_subset k A T hk)
    (volume_pi_Icc_lt_top k T)).integrableOn

/-- The set difference `pi Ici 0 \ pi Ioi 0` lies in the union of coordinate hyperplanes. -/
lemma diff_pi_Ici_pi_Ioi_subset_iUnion_hyperplanes {k : ℕ} :
    (Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ))) \
      (Set.univ.pi (fun _ : Fin k ↦ Set.Ioi (0 : ℝ))) ⊆
    ⋃ i : Fin k, {t : Fin k → ℝ | t i = 0} := by
  intro t ⟨ht1, ht2⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Ici] at ht1
  rw [Set.mem_pi] at ht2
  push Not at ht2
  obtain ⟨i, _, hi⟩ := ht2
  simp only [Set.mem_Ioi, not_lt] at hi
  exact Set.mem_iUnion.mpr ⟨i, le_antisymm hi (ht1 i)⟩

/-- Each coordinate hyperplane has measure zero in $\mathbb{R}^k$. -/
lemma volume_coord_eq_zero {k : ℕ} (i : Fin k) : volume {t : Fin k → ℝ | t i = 0} = 0 := by
  have hset : {t : Fin k → ℝ | t i = 0} =
      Set.univ.pi (fun j : Fin k ↦ if j = i then ({0} : Set ℝ) else Set.univ) := by
    ext t
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    refine ⟨fun hi j ↦ ?_, fun h ↦ by simpa using h i⟩
    by_cases hj : j = i
    · subst hj
      simp [hi]
    · simp [hj]
  rw [hset, volume_pi, MeasureTheory.Measure.pi_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- The product sets `pi Ici 0` and `pi Ioi 0` are a.e. equal. -/
lemma pi_Ici_ae_eq_pi_Ioi (k : ℕ) : (Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ))) =ᵐ[volume]
    (Set.univ.pi (fun _ : Fin k ↦ Set.Ioi (0 : ℝ))) := by
  rw [MeasureTheory.ae_eq_set]
  refine ⟨?_, ?_⟩
  · refine measure_mono_null diff_pi_Ici_pi_Ioi_subset_iUnion_hyperplanes ?_
    rw [MeasureTheory.measure_iUnion_null_iff]
    exact volume_coord_eq_zero
  · have hsub : (Set.univ.pi (fun _ : Fin k ↦ Set.Ioi (0 : ℝ))) ⊆
        (Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ))) :=
      fun _ ht i hi ↦ Set.mem_Ici.mpr (ht i hi).le
    rw [Set.sdiff_eq_empty.mpr hsub]
    exact measure_empty

/-- The integral over `simplexPi k 1` is at most the integral over the nonnegative orthant. -/
lemma setIntegral_simplex_le_pi_Ici (k : ℕ) (A T : ℝ) (hk : 0 < k) (hA : 0 < A) :
    ∫ t in PrimeGaps.simplexPi k 1, ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 ≤
      ∫ t in Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ)), ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 :=
  MeasureTheory.setIntegral_mono_set (integrable_prod_g_sq_pi_Ici k A T hk hA)
    (Filter.Eventually.of_forall (prod_g_sq_nonneg k A T))
    (simplex_subset_pi_Ici k).eventuallyLE

/-- Replacing `pi Ici 0` by `pi Ioi 0` does not change the integral. -/
lemma setIntegral_pi_Ici_eq_pi_Ioi (k : ℕ) (A T : ℝ) :
    ∫ t in Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ)), ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 =
    ∫ t in Set.univ.pi (fun _ : Fin k ↦ Set.Ioi (0 : ℝ)), ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 :=
  MeasureTheory.setIntegral_congr_set (pi_Ici_ae_eq_pi_Ioi k)

/-- The indicator of a product set applied to a product of values factors
into a product of one-dimensional indicators. -/
lemma pi_indicator_prod_eq (k : ℕ) (s : Set ℝ) (h : ℝ → ℝ) (t : Fin k → ℝ) :
    (Set.univ.pi (fun _ : Fin k ↦ s)).indicator (fun t ↦ ∏ i, h (t i)) t =
      ∏ i, s.indicator h (t i) := by
  by_cases ht : t ∈ Set.univ.pi (fun _ : Fin k ↦ s)
  · rw [Set.indicator_of_mem ht]
    refine Finset.prod_congr rfl fun i _ ↦ ?_
    rw [Set.indicator_of_mem (ht i (Set.mem_univ _))]
  · rw [Set.indicator_of_notMem ht]
    rw [Set.mem_univ_pi] at ht
    push Not at ht
    obtain ⟨i₀, hi₀⟩ := ht
    exact (Finset.prod_eq_zero (Finset.mem_univ i₀) (Set.indicator_of_notMem hi₀ _)).symm

/-- Set integral over a product set as integral of product of indicators. -/
lemma setIntegral_pi_eq_integral_prod_indicator (k : ℕ) (s : Set ℝ) (h : ℝ → ℝ)
    (hs : MeasurableSet s) :
    (∫ t in Set.univ.pi (fun _ : Fin k ↦ s), ∏ i, h (t i)) =
      ∫ t : Fin k → ℝ, ∏ i, s.indicator h (t i) := by
  rw [← integral_indicator (MeasurableSet.univ_pi fun _ ↦ hs)]
  exact integral_congr_ae (Filter.Eventually.of_forall (pi_indicator_prod_eq k s h))

/-- Integral over $(0,\infty)^k$ of $\prod_i g(kt_i)^2$ is the $k$-th power of the
one-dimensional integral. -/
lemma setIntegral_pi_Ioi_eq_prod_pow (k : ℕ) (A T : ℝ) :
    ∫ t in Set.univ.pi (fun _ : Fin k ↦ Set.Ioi (0 : ℝ)), ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 =
      (∫ t in Set.Ioi (0 : ℝ), (g A T ((k : ℝ) * t)) ^ 2) ^ k := by
  set s : Set ℝ := Set.Ioi (0 : ℝ)
  set h : ℝ → ℝ := fun t ↦ (g A T ((k : ℝ) * t)) ^ 2
  rw [show (∫ t in Set.univ.pi (fun _ : Fin k ↦ Set.Ioi (0 : ℝ)),
            ∏ i, (g A T ((k : ℝ) * t i)) ^ 2) =
          ∫ t in Set.univ.pi (fun _ : Fin k ↦ s), ∏ i, h (t i) from rfl,
      setIntegral_pi_eq_integral_prod_indicator k s h measurableSet_Ioi,
      MeasureTheory.integral_fintype_prod_volume_eq_prod (fun _ : Fin k ↦ s.indicator h),
      MeasureTheory.integral_indicator measurableSet_Ioi,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The simplex-domain integral is bounded by the $k$-th power of the one-dimensional integral. -/
lemma I_le_integral_pow (k : ℕ) (A T : ℝ) (hk : 2 ≤ k) (hA : 0 < A) :
    I k A T ≤ (∫ t in Set.Ioi (0 : ℝ), (g A T ((k : ℝ) * t)) ^ 2) ^ k :=
  calc I k A T = ∫ t in PrimeGaps.simplexPi k 1, ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 := rfl
    _ ≤ ∫ t in Set.univ.pi (fun _ : Fin k ↦ Set.Ici (0 : ℝ)), ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 :=
        setIntegral_simplex_le_pi_Ici k A T (by omega) hA
    _ = ∫ t in Set.univ.pi (fun _ : Fin k ↦ Set.Ioi (0 : ℝ)), ∏ i, (g A T ((k : ℝ) * t i)) ^ 2 :=
        setIntegral_pi_Ici_eq_pi_Ioi k A T
    _ = (∫ t in Set.Ioi (0 : ℝ), (g A T ((k : ℝ) * t)) ^ 2) ^ k :=
        setIntegral_pi_Ioi_eq_prod_pow k A T

/-- The $k$-th power of the one-dimensional integral is $k^{-k}\gamma^k$. -/
lemma integral_g_sq_kt_pow (k : ℕ) (A T : ℝ) (hk : 2 ≤ k) (hT : 0 ≤ T) :
    (∫ t in Set.Ioi (0 : ℝ), (g A T ((k : ℝ) * t)) ^ 2) ^ k =
      ((k : ℝ) ^ k)⁻¹ * (A1_MuClosedForm.gamma A T) ^ k := by
  rw [integral_g_sq_kt k A T hk hT, div_pow]
  have hkne : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  field_simp

/-- The simplex integral bound: for $k \ge 2$, $A > 0$, $T > 0$,
$I_k \le k^{-k}\bigl(A^{-1}(1 - (1 + AT)^{-1})\bigr)^k$. -/
theorem simplex_integral_bound (k : ℕ) (A T : ℝ) (hk : 2 ≤ k) (hA : 0 < A) (hT : 0 < T) :
    I k A T ≤ ((k : ℝ) ^ k)⁻¹ * ((1 / A) * (1 - 1 / (1 + A * T))) ^ k := by
  rw [← A1_MuClosedForm.gamma_formula A T hA hT, ← integral_g_sq_kt_pow k A T hk hT.le]
  exact I_le_integral_pow k A T hk hA

end SimplexIntegralBound

end PrimeGaps.M016Asymp.B1_IkTensorUpperBound

end
