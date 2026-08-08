/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Integral.Pi
public import PrimeGapsTheory.Variational.M016Asymp.GPositive

/-!
# Diagonal truncation bound for the `Eₖ` integral

For a nonnegative weight `h` supported on `[0, T]`, bounds the diagonal-truncation
integral `∫ (u j)² ∏ᵢ h(uᵢ)` over `(Set.Ici 0)^{k-1}` by `T · μγ h · (γ h)^{k-2}`.

## Main definitions

* `γ`: The total mass `∫₀^∞ h(u) du`.
* `μγ`: The first moment `∫₀^∞ u · h(u) du`.

## Main results

* `integral_sq_mul_prod_le`: The diagonal-truncation bound
  `∫ (u j)² ∏ᵢ h(uᵢ) ≤ T · μγ h · (γ h)^{k-2}`.
-/

@[expose] public section

open scoped Finset

namespace PrimeGaps.M016Asymp.C1b_EkDiagonalTruncation

open MeasureTheory
open PrimeGaps.M016Asymp.A0_GPositive

/-- The total mass `γ := ∫_0^∞ h(u) du`. -/
@[nolint defsWithUnderscore]
noncomputable def γ (h : ℝ → ℝ) : ℝ := ∫ u in Set.Ici (0 : ℝ), h u

/-- The first moment `μγ := ∫_0^∞ u * h(u) du`. -/
@[nolint defsWithUnderscore]
noncomputable def μγ (h : ℝ → ℝ) : ℝ := ∫ u in Set.Ici (0 : ℝ), u * h u

/-- If `h` is nonnegative, then `γ h` is nonnegative. -/
lemma γ_nonneg (h : ℝ → ℝ) (hnn : ∀ u, 0 ≤ h u) : 0 ≤ γ h := integral_nonneg hnn

/-- For `u ∈ [0,∞)`, `u^2 * h u ≤ T * (u * h u)`. -/
lemma pointwise_u_sq_h_le (T : ℝ) (h : ℝ → ℝ) (hnn : ∀ u, 0 ≤ h u)
    (hsupp_pos : ∀ u, T < u → h u = 0)
    (u : ℝ) (hu : 0 ≤ u) :
    u ^ 2 * h u ≤ T * (u * h u) := by
  by_cases hT : u ≤ T
  · nlinarith [hnn u, sq_nonneg u, mul_nonneg hu (hnn u)]
  · simp [hsupp_pos u (not_le.mp hT)]

/-- The function `u ↦ u^2 * h u` is integrable on `[0,∞)`. -/
lemma integrable_u_sq_h_Ici (T : ℝ) (hT : 0 < T) (h : ℝ → ℝ) (hmeas : Measurable h)
    (hnn : ∀ u, 0 ≤ h u)
    (hsupp_pos : ∀ u, T < u → h u = 0)
    (hint_uh : IntegrableOn (fun u ↦ u * h u) (Set.Ici (0 : ℝ))) :
    IntegrableOn (fun u ↦ u ^ 2 * h u) (Set.Ici (0 : ℝ)) := by
  have hg_int : IntegrableOn (fun u ↦ T * (u * h u)) (Set.Ici (0 : ℝ)) := hint_uh.const_mul T
  have hf_meas : Measurable (fun u : ℝ ↦ u ^ 2 * h u) := (measurable_id.pow_const 2).mul hmeas
  refine Integrable.mono hg_int hf_meas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ici).mpr (Filter.Eventually.of_forall (fun u hu ↦ ?_))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (hnn u)),
      abs_of_nonneg (mul_nonneg hT.le (mul_nonneg hu (hnn u)))]
  exact pointwise_u_sq_h_le T h hnn hsupp_pos u hu

/-- The pointwise bound `u² · h u ≤ T · u · h u` for `h` supported on `[0, T]`. -/
lemma u_sq_h_le_T_u_h
    (T : ℝ) (h : ℝ → ℝ)
    (hnn : ∀ u, 0 ≤ h u)
    (hsupp_pos : ∀ u, T < u → h u = 0)
    (hsupp_neg : ∀ u, u < 0 → h u = 0)
    (u : ℝ) : u ^ 2 * h u ≤ T * u * h u := by
  rcases le_or_gt 0 u with hu | hu
  · rw [mul_assoc]
    exact pointwise_u_sq_h_le T h hnn hsupp_pos u hu
  · simp [hsupp_neg u hu]

/-- The integral `∫_0^∞ u^2 · h(u) du` is bounded by `T · μγ h`. -/
lemma integral_u_sq_h_le (T : ℝ) (hT : 0 < T) (h : ℝ → ℝ) (hmeas : Measurable h)
    (hnn : ∀ u, 0 ≤ h u)
    (hsupp_pos : ∀ u, T < u → h u = 0)
    (hsupp_neg : ∀ u, u < 0 → h u = 0)
    (hint_uh : IntegrableOn (fun u ↦ u * h u) (Set.Ici (0 : ℝ))) :
    ∫ u in Set.Ici (0 : ℝ), u ^ 2 * h u ≤ T * μγ h := by
  have h_int_u2h : IntegrableOn (fun u ↦ u ^ 2 * h u) (Set.Ici (0 : ℝ)) :=
    integrable_u_sq_h_Ici T hT h hmeas hnn hsupp_pos hint_uh
  have h_int_Tuh : IntegrableOn (fun u ↦ T * u * h u) (Set.Ici (0 : ℝ)) := by
    have : IntegrableOn (fun u ↦ T * (u * h u)) (Set.Ici (0 : ℝ)) := hint_uh.const_mul T
    simpa [mul_assoc] using this
  have h_mono : ∫ u in Set.Ici (0 : ℝ), u ^ 2 * h u ≤ ∫ u in Set.Ici (0 : ℝ), T * u * h u :=
    MeasureTheory.integral_mono_ae h_int_u2h h_int_Tuh
      (Filter.Eventually.of_forall
        (fun u ↦ u_sq_h_le_T_u_h T h hnn hsupp_pos hsupp_neg u))
  have h_factor : ∫ u in Set.Ici (0 : ℝ), T * u * h u = T * μγ h := by
    unfold μγ
    rw [show (fun u : ℝ ↦ T * u * h u) = (fun u ↦ T * (u * h u)) from
      funext fun u ↦ by ring]
    exact MeasureTheory.integral_const_mul T (fun u ↦ u * h u)
  linarith

/-- At index `j`, `fComp h j i u = u ^ 2 * h u`; at every other index it equals `h u`. -/
@[nolint defsWithUnderscore]
noncomputable def fComp (h : ℝ → ℝ) {k : ℕ} (j : Fin (k - 1)) (i : Fin (k - 1)) (u : ℝ) : ℝ :=
  if i = j then u ^ 2 * h u else h u

/-- The integrand `(u j)^2 * ∏ i, h (u i)` equals `∏ i, fComp h j i (u i)`. -/
lemma integrand_eq_prod (k : ℕ) (h : ℝ → ℝ) (j : Fin (k - 1)) (u : Fin (k - 1) → ℝ) :
    (u j) ^ 2 * ∏ i, h (u i) = ∏ i, fComp h j i (u i) := by
  rw [← Finset.mul_prod_erase _ (fun i ↦ fComp h j i (u i)) (Finset.mem_univ j),
      ← Finset.mul_prod_erase _ (fun i ↦ h (u i)) (Finset.mem_univ j),
      show fComp h j j (u j) = (u j) ^ 2 * h (u j) by simp [fComp]]
  have hother : ∀ i ∈ Finset.univ.erase j, fComp h j i (u i) = h (u i) := by
    intro i hi
    simp [fComp, (Finset.mem_erase.mp hi).1]
  rw [Finset.prod_congr rfl hother]
  ring

/-- The integral of `∏ i, fComp h j i (u i)` over the product measure equals the
product of the integrals of its factors. -/
lemma integral_pi_prod_factor (k : ℕ) (h : ℝ → ℝ) (hmeas : Measurable h) (hnn : ∀ u, 0 ≤ h u)
    (hint_h : IntegrableOn h (Set.Ici (0 : ℝ)))
    (hint_u2h : IntegrableOn (fun u ↦ u ^ 2 * h u) (Set.Ici (0 : ℝ)))
    (j : Fin (k - 1)) :
    ∫ u : Fin (k - 1) → ℝ, ∏ i, fComp h j i (u i)
        ∂(MeasureTheory.Measure.pi
            (fun _ : Fin (k - 1) ↦ (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))) =
      ∏ i, ∫ u in Set.Ici (0 : ℝ), fComp h j i u := by
  let _ := hmeas; let _ := hnn; let _ := hint_h; let _ := hint_u2h
  exact integral_fintype_prod_eq_prod (fun i ↦ fComp h j i)

/-- For `i ≠ j`, the integral of `fComp h j i` over `[0,∞)` equals `γ h`. -/
lemma integral_fComp_ne (h : ℝ → ℝ) {k : ℕ} (j i : Fin (k - 1)) (hij : i ≠ j) :
    ∫ u in Set.Ici (0 : ℝ), fComp h j i u = γ h := by
  unfold fComp γ
  simp [if_neg hij]

/-- The integral of `fComp h j j` over `[0,∞)` equals `∫_0^∞ u^2 · h(u) du`. -/
lemma integral_fComp_eq (h : ℝ → ℝ) {k : ℕ} (j : Fin (k - 1)) :
    ∫ u in Set.Ici (0 : ℝ), fComp h j j u = ∫ u in Set.Ici (0 : ℝ), u ^ 2 * h u := by
  simp [fComp]

/-- The product of the component integrals equals the second moment times
`(γ h) ^ (k - 2)`. -/
lemma prod_fComp_factor (k : ℕ) (hk : 2 ≤ k) (h : ℝ → ℝ) (j : Fin (k - 1)) :
    (∏ i, ∫ u in Set.Ici (0 : ℝ), fComp h j i u) =
      (∫ u in Set.Ici (0 : ℝ), u ^ 2 * h u) * (γ h) ^ (k - 2) := by
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin (k - 1)))
        (fun i ↦ ∫ u in Set.Ici (0 : ℝ), fComp h j i u) (Finset.mem_univ j),
      integral_fComp_eq h j,
      Finset.prod_congr rfl (fun i hi ↦ integral_fComp_ne h j i (Finset.mem_erase.mp hi).1),
      Finset.prod_const]
  have hcard : #(Finset.univ.erase j) = k - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    omega
  rw [hcard]

/-- Product-measure factorization of the integral. -/
lemma integral_pi_factorize (k : ℕ) (hk : 2 ≤ k) (h : ℝ → ℝ) (hmeas : Measurable h)
    (hnn : ∀ u, 0 ≤ h u)
    (hint_h : IntegrableOn h (Set.Ici (0 : ℝ)))
    (hint_u2h : IntegrableOn (fun u ↦ u ^ 2 * h u) (Set.Ici (0 : ℝ)))
    (j : Fin (k - 1)) :
    ∫ u : Fin (k - 1) → ℝ, (u j) ^ 2 * ∏ i, h (u i)
        ∂(MeasureTheory.Measure.pi
            (fun _ : Fin (k - 1) ↦ (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))) =
      (∫ u in Set.Ici (0 : ℝ), u ^ 2 * h u) * (γ h) ^ (k - 2) := by
  have hrw : (fun u : Fin (k - 1) → ℝ ↦ (u j) ^ 2 * ∏ i, h (u i)) =
        (fun u : Fin (k - 1) → ℝ ↦ ∏ i, fComp h j i (u i)) :=
    funext fun u ↦ integrand_eq_prod k h j u
  rw [hrw, integral_pi_prod_factor k h hmeas hnn hint_h hint_u2h j, prod_fComp_factor k hk h j]

/-- **Diagonal truncation bound.** For a nonnegative weight `h` supported on `[0, T]` with
`h` and `u ↦ u · h u` integrable on `[0, ∞)`, the diagonal integral
`∫ (u j)² ∏ᵢ h(uᵢ)` over `(Set.Ici 0)^{k-1}` is bounded by `T · μγ h · (γ h)^{k-2}`. -/
theorem integral_sq_mul_prod_le (k : ℕ) (hk : 2 ≤ k) (T : ℝ) (hT : 0 < T)
    (h : ℝ → ℝ) (hmeas : Measurable h)
    (hnn : ∀ u, 0 ≤ h u)
    (hsupp_pos : ∀ u, T < u → h u = 0)
    (hsupp_neg : ∀ u, u < 0 → h u = 0)
    (hint_h : IntegrableOn h (Set.Ici (0 : ℝ)))
    (hint_uh : IntegrableOn (fun u ↦ u * h u) (Set.Ici (0 : ℝ)))
    (j : Fin (k - 1)) :
    ∫ u : Fin (k - 1) → ℝ, (u j) ^ 2 * ∏ i, h (u i)
        ∂(MeasureTheory.Measure.pi
            (fun _ : Fin (k - 1) ↦ (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))) ≤
      T * μγ h * (γ h) ^ (k - 2) := by
  have hint_u2h : IntegrableOn (fun u ↦ u ^ 2 * h u) (Set.Ici (0 : ℝ)) :=
    integrable_u_sq_h_Ici T hT h hmeas hnn hsupp_pos hint_uh
  have hfact : ∫ u : Fin (k - 1) → ℝ, (u j) ^ 2 * ∏ i, h (u i)
          ∂(MeasureTheory.Measure.pi
              (fun _ : Fin (k - 1) ↦ (volume : Measure ℝ).restrict (Set.Ici (0 : ℝ)))) =
        (∫ u in Set.Ici (0 : ℝ), u ^ 2 * h u) * (γ h) ^ (k - 2) :=
    integral_pi_factorize k hk h hmeas hnn hint_h hint_u2h j
  have hbd : ∫ u in Set.Ici (0 : ℝ), u ^ 2 * h u ≤ T * μγ h :=
    integral_u_sq_h_le T hT h hmeas hnn hsupp_pos hsupp_neg hint_uh
  have hγnn : 0 ≤ (γ h) ^ (k - 2) := pow_nonneg (γ_nonneg h hnn) _
  rw [hfact]
  exact mul_le_mul_of_nonneg_right hbd hγnn

end PrimeGaps.M016Asymp.C1b_EkDiagonalTruncation

end
