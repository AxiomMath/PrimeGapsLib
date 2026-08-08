/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Analysis.Tonelli.EuclideanLemmas
public import PrimeGapsTheory.Analysis.Tonelli.LpGeneral

import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls


/-!
# Tonelli operators on Lᵖ(ℝⁿ)

For an index `m : Fin k` and a set `S ⊆ ℝ^(n-1) × ℝ` with essentially finite fibres, we define
`Lᵖ(ℝ^n restricted to the S-region) → Lᵖ(ℝ^(n-1))` given by `f ↦ (x ↦ ∫ f dxₘ)`.
This is a continuous linear operator, called `MeasureTheory.Lp.integralVarCLM`.
-/

@[expose] public section

open Fin
open ENNReal MeasureTheory Measure EuclideanSpace

local notation "ES(" 𝕜:65 ", " k:65 ")" => EuclideanSpace 𝕜 (Fin k)

-- belongs to mathlib
theorem EuclideanSpace.volume_ball_fin_one (x : ES(ℝ, 1)) (r : ℝ) :
    volume (Metric.ball x r) = 2 * .ofReal r := by
  rw [mul_comm]
  norm_num [InnerProductSpace.volume_ball_of_dim_odd (k := 0) (by simp) x]

-- belongs to mathlib
theorem EuclideanSpace.volume_closedBall_fin_one (x : ES(ℝ, 1)) (r : ℝ) :
    volume (Metric.closedBall x r) = 2 * .ofReal r := by
  rw [addHaar_closedBall_eq_addHaar_ball, volume_ball_fin_one x r]

namespace MeasureTheory

variable {p : ℝ≥0∞} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The coordinate isomorphism carries the restriction to the image of `S` back to the
restriction to `S`. -/
theorem measurePreserving_symm_finIsolateEquivProd_restrict {k : ℕ} (m : Fin k)
    {S : Set ES(ℝ, k)} (hMS : MeasurableSet S) :
    MeasurePreserving (finIsolateEquivProd ℝ m).symm
      (volume.restrict (finIsolateEquivProd ℝ m '' S)) (volume.restrict S) := by
  rw [(finIsolateEquivProd ℝ m).image_eq_preimage_symm]
  exact (measurePreserving_symm_finIsolateEquivProd m).restrict_preimage hMS

/-- The image of a measurable set under the coordinate isomorphism is measurable. -/
theorem measurableSet_image_finIsolateEquivProd {k : ℕ} (m : Fin k) {S : Set ES(ℝ, k)}
    (hMS : MeasurableSet S) : MeasurableSet (finIsolateEquivProd ℝ m '' S) :=
  (finIsolateEquivProd ℝ m).toHomeomorph.measurableEmbedding.measurableSet_image.mpr hMS

/-- Integration along the chosen variable `m`, as a continuous linear map on the part of
`Lᵖ(ℝ^k)` supported on a set `S` whose image under the coordinate isomorphism has essentially
finite fibres. -/
noncomputable def Lp.integralVarCLM [Fact (1 ≤ p)] {k : ℕ} (m : Fin k)
    {S : Set ES(ℝ, k)} (hMS : MeasurableSet S)
    (hS : EssFiniteSnd (finIsolateEquivProd ℝ m '' S) volume volume) :
    Lp E p (volume.restrict S) →L[ℝ] Lp E p (volume (α := ES(ℝ, k - 1))) :=
  integralLeftCLM (measurableSet_image_finIsolateEquivProd m hMS) hS ∘L
    (compMeasurePreservingₗᵢ _ _
      (measurePreserving_symm_finIsolateEquivProd_restrict m hMS)).toContinuousLinearMap

theorem Lp.norm_integralVarCLM_le [Fact (1 ≤ p)] (q : ℝ≥0∞) [p.HolderConjugate q]
    {k : ℕ} {m : Fin k} {S : Set ES(ℝ, k)} {hMS : MeasurableSet S}
    {hS : EssFiniteSnd (finIsolateEquivProd ℝ m '' S) volume volume}
    {f : Lp E p (volume.restrict S)} :
    ‖Lp.integralVarCLM m hMS hS f‖ ≤
      (essSupSnd (finIsolateEquivProd ℝ m '' S) volume volume ^ q⁻¹.toReal).toReal * ‖f‖ := by
  have h := Lp.norm_integralLeftCLM_le (E := E) q
    (hMS := measurableSet_image_finIsolateEquivProd m hMS) (hS := hS)
    (f := (compMeasurePreservingₗᵢ ℝ _
      (measurePreserving_symm_finIsolateEquivProd_restrict m hMS)).toContinuousLinearMap f)
  aesop

theorem essSupSnd_le_of_subset_closedBall
    {k : ℕ} {S : Set ES(ℝ, k)} {r : ℝ} (hr : S ⊆ Metric.closedBall 0 r)
    {m : Fin k} : essSupSnd (finIsolateEquivProd ℝ m '' S) volume volume ≤ 2 * .ofReal r := by
  refine essSup_le_of_ae_le _ <| ae_of_all _ fun x ↦ ?_
  dsimp only
  rw [← volume_closedBall_fin_one 0]
  refine measure_mono fun y hy ↦ ?_
  obtain ⟨z, hzS, hz⟩ := hy
  have hzball := hr hzS
  rw [Metric.mem_closedBall, dist_zero_right] at hzball ⊢
  have hyz : y 0 = z m := by
    simpa [finIsolateEquivProd, sumEquivProd, finIsolateEquivSum] using
      (congrArg (fun q : ES(ℝ, k - 1) × ES(ℝ, 1) ↦ q.2 0) hz).symm
  calc ‖y‖
      = ‖y 0‖ := by
        rw [EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.norm_eq_abs, sq_abs]
        exact Real.sqrt_sq_eq_abs _
    _ = ‖z m‖ := by rw [hyz]
    _ ≤ ‖z‖ := PiLp.norm_apply_le z m
    _ ≤ r := hzball

theorem EssFiniteSnd.of_isBounded
    {k : ℕ} {S : Set ES(ℝ, k)} (hS : Bornology.IsBounded S)
    {m : Fin k} : EssFiniteSnd (finIsolateEquivProd ℝ m '' S) volume volume := by
  obtain ⟨_, hr⟩ := (Metric.isBounded_iff_subset_closedBall 0).mp hS
  exact ((essSupSnd_le_of_subset_closedBall hr).trans_lt (mul_lt_top ofNat_lt_top ofReal_lt_top)).ne

theorem EssFiniteSnd.of_bounded
    {k : ℕ} {S : Set ES(ℝ, k)} {M : ℝ} (hS : ∀ x ∈ S, ‖x‖ ≤ M)
    {m : Fin k} : EssFiniteSnd (finIsolateEquivProd ℝ m '' S) volume volume :=
  .of_isBounded <| isBounded_iff_forall_norm_le.mpr ⟨_, hS⟩

theorem EssFiniteSnd.of_isCompact
    {k : ℕ} {S : Set ES(ℝ, k)} (hS : IsCompact S)
    {m : Fin k} : EssFiniteSnd (finIsolateEquivProd ℝ m '' S) volume volume :=
  .of_isBounded hS.isBounded

end MeasureTheory
