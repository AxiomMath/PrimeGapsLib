/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.Tonelli.EuclideanLemmas
public import PrimeGapsTheory.Analysis.Tonelli.L1General


/-! # Tonelli operators on L¹(ℝⁿ)

For any index `k` we define `L¹(ℝ^n) → L¹(ℝ^(n-1))` given by `f ↦ (x ↦ ∫ f dxₖ)`.
This is a continuous linear operator, called `MeasureTheory.L1.integralVarCLM`.
-/

@[expose] public section

open MeasureTheory EuclideanSpace

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

/-- Integration along a chosen variable. -/
noncomputable def MeasureTheory.L1.integralVarCLM
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : ℕ} (m : Fin k) :
    Lp E 1 (volume (α := ES(ℝ, k))) →L[ℝ] Lp E 1 (volume (α := ES(ℝ, k - 1))) :=
  integralLeftCLM ∘L (Lp.compMeasurePreservingₗᵢ _ _
    (measurePreserving_symm_finIsolateEquivProd m)).toContinuousLinearMap
