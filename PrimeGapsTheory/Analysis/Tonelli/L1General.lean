/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Integral.Prod


/-! # Tonelli operator on L¹

We define `L¹(α × β) → L¹(α)` given by `f ↦ (x ↦ ∫ y, f(x, y) ∂ν)`.
This is a continuous linear operator, called `MeasureTheory.L1.integralLeftCLM`.
-/

@[expose] public section

open MeasureTheory Measure

namespace MeasureTheory

variable {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
  [NormedAddCommGroup E] [SFinite ν] [NormedSpace ℝ E]

theorem memL1_integral_left {f : α × β → E} (hf : MemLp f 1 (μ.prod ν)) :
    MemLp (fun x ↦ ∫ y, f (x, y) ∂ν) 1 μ := by
  rw [memLp_one_iff_integrable] at hf ⊢
  exact hf.integral_prod_left

/-- Integration along the second variable. -/
noncomputable def L1.integralLeftₗ [SFinite μ] : Lp E 1 (μ.prod ν) →ₗ[ℝ] Lp E 1 μ where
  toFun f := (L1.integrable_coeFn f).integral_prod_left.toL1
  map_add' f g := Lp.ext <| by
    filter_upwards [ae_ae_of_ae_prod (Lp.coeFn_add f g),
      Lp.coeFn_add (L1.integrable_coeFn f).integral_prod_left.toL1
        (L1.integrable_coeFn g).integral_prod_left.toL1,
      (L1.integrable_coeFn f).integral_prod_left.coeFn_toL1,
      (L1.integrable_coeFn g).integral_prod_left.coeFn_toL1,
      (L1.integrable_coeFn (f + g)).integral_prod_left.coeFn_toL1,
      (L1.integrable_coeFn f).prod_right_ae, (L1.integrable_coeFn g).prod_right_ae]
      with x h₁ h₂ h₃ h₄ h₅ h₆ h₇
    rw [h₂, Pi.add_apply, h₃, h₄, h₅, ← MeasureTheory.integral_add h₆ h₇]
    exact integral_congr_ae h₁
  map_smul' c f := Lp.ext <| by
    filter_upwards [ae_ae_of_ae_prod (Lp.coeFn_smul c f),
      Lp.coeFn_smul c (L1.integrable_coeFn f).integral_prod_left.toL1,
      (L1.integrable_coeFn f).integral_prod_left.coeFn_toL1,
      (L1.integrable_coeFn (c • f)).integral_prod_left.coeFn_toL1,
      (L1.integrable_coeFn f).prod_right_ae]
      with x h₁ h₂ h₃ h₄ h₅
    rw [RingHom.id_apply, h₂, Pi.smul_apply, h₃, h₄, ← MeasureTheory.integral_smul]
    exact integral_congr_ae h₁

theorem L1.coeFn_integralLeftₗ [SFinite μ] (f : Lp E 1 (μ.prod ν)) :
    ∀ᵐ x ∂μ, integralLeftₗ f x = ∫ y, f (x, y) ∂ν :=
  (L1.integrable_coeFn f).integral_prod_left.coeFn_toL1

theorem L1.norm_integralLeftₗ_le [SFinite μ] (f : Lp E 1 (μ.prod ν)) :
    ∀ᵐ x ∂μ, ‖integralLeftₗ f x‖ ≤ ∫ y, ‖f (x, y)‖ ∂ν := by
  filter_upwards [coeFn_integralLeftₗ f, (L1.integrable_coeFn f).prod_right_ae] with x h₁ h₂
  grw [h₁, norm_integral_le_integral_norm]

/-- Partial integration along the second variable. -/
noncomputable def L1.integralLeftCLM [SFinite μ] : Lp E 1 (μ.prod ν) →L[ℝ] Lp E 1 μ :=
  integralLeftₗ.mkContinuous 1 fun f ↦ by
    simp_rw [L1.norm_eq_integral_norm, one_mul, integral_prod _ (L1.integrable_coeFn f).norm]
    exact integral_mono_ae (L1.integrable_coeFn _).norm
      (L1.integrable_coeFn f).norm.integral_prod_left (norm_integralLeftₗ_le f)

theorem L1.coeFn_integralLeftCLM [SFinite μ] (f : Lp E 1 (μ.prod ν)) :
    ∀ᵐ x ∂μ, integralLeftCLM f x = ∫ y, f (x, y) ∂ν :=
  coeFn_integralLeftₗ f

end MeasureTheory
