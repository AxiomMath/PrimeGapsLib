/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Variational.MkRatio

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Smooth witnesses for the variational quotient

Approximates variational quotients by smooth simplex-supported functions and proves the resulting
variational inequalities.

## Main definitions

* `rayleigh`: The quotient of the sum of marginal quadratic forms by the norm quadratic form.

## Main results

* `exists_smooth_ratio_close`: Gives a smooth function with nearly the same Rayleigh quotient.
* `maynard_smooth_witness_ineq`: Gives a smooth function satisfying the variational inequality.
* `M_pos_and_le_and_exists_smooth_lt_sum_J`: Bounds `M k` and approximates it by smooth
  simplex-supported functions.
-/

@[expose] public section

open MeasureTheory EuclideanSpace
open scoped PrimeGaps

namespace PrimeGaps
open PropM105

/-- The Rayleigh quotient as a function on `Lp`. -/
noncomputable def rayleigh (k : ℕ) (g : Lp ℝ 2 (volume.restrict (𝓡 k))) : ℝ :=
  (∑ m, PrimeGaps.J m g) / ‖g‖ ^ 2

/-- The numerator `g ↦ ∑ m, J m g` of the Rayleigh quotient is continuous. -/
theorem continuous_rayleigh_num (k : ℕ) :
    Continuous (fun g : Lp ℝ 2 (volume.restrict (𝓡 k)) ↦ ∑ m, PrimeGaps.J m g) :=
  continuous_finsetSum _ (fun m _ ↦ PrimeGaps.continuous_J m)

/-- `rayleigh k` is continuous at any `f` of nonzero norm. -/
theorem continuousAt_rayleigh (k : ℕ) (f : Lp ℝ 2 (volume.restrict (𝓡 k)))
    (hI : ‖f‖ ^ 2 ≠ 0) : ContinuousAt (rayleigh k) f :=
  (continuous_rayleigh_num k).continuousAt.div (continuous_norm.pow 2).continuousAt hI

/-- `dist (hmem₁.toLp F₁) f` in `Lp` equals the `L²` distance `‖⇑f - F₁‖`. -/
theorem dist_toLp_eq_eLpNorm {k : ℕ}
    (f : Lp ℝ 2 (volume.restrict (𝓡 k))) (F₁ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hmem₁ : MemLp F₁ 2 (volume.restrict (𝓡 k))) :
    dist (hmem₁.toLp F₁) f =
      (eLpNorm (fun x ↦ f x - F₁ x) 2 (volume.restrict (𝓡 k))).toReal := by
  rw [Lp.dist_def]
  have hae : (⇑(hmem₁.toLp F₁) - ⇑f) =ᵐ[volume.restrict (𝓡 k)] (-(fun x ↦ f x - F₁ x)) := by
    filter_upwards [hmem₁.coeFn_toLp] with x hx
    simp only [Pi.sub_apply, Pi.neg_apply, hx]; ring
  rw [eLpNorm_congr_ae hae, eLpNorm_neg]

/-- A positive-norm `L²` function has a smooth simplex-supported approximant whose Rayleigh
quotient differs by less than `η`. -/
@[pg_tag "bg246" "lem_density_smooth"]
theorem exists_smooth_ratio_close (k : ℕ) (hk : 2 ≤ k)
    (f : Lp ℝ 2 (volume.restrict (𝓡 k))) (hIf : 0 < ‖f‖ ^ 2)
    {η : ℝ} (hη : 0 < η) :
    ∃ F : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      tsupport F ⊆ 𝓡 k ∧ ∃ hmem : MemLp F 2 (volume.restrict (𝓡 k)), 0 < ‖hmem.toLp F‖ ^ 2 ∧
        |rayleigh k (hmem.toLp F) - rayleigh k f| < η := by
  have hcontR : ContinuousAt (rayleigh k) f := continuousAt_rayleigh k f (ne_of_gt hIf)
  rw [Metric.continuousAt_iff] at hcontR
  obtain ⟨δr, hδrpos, hδr⟩ := hcontR η hη
  have hcontI : ContinuousAt (fun g ↦ ‖g‖ ^ 2) f := (continuous_norm.pow 2).continuousAt
  rw [Metric.continuousAt_iff] at hcontI
  obtain ⟨δI, hδIpos, hδI⟩ := hcontI (‖f‖ ^ 2) hIf
  have hδpos : 0 < min δr δI := lt_min hδrpos hδIpos
  obtain ⟨F₁, hCD, hsupp, hclose⟩ := smooth_L2_approx_on_simplex k hk (⇑f) (Lp.memLp f) _ hδpos
  have hmem₁ : MemLp F₁ 2 (volume.restrict (𝓡 k)) :=
    hCD.continuous.memLp_of_hasCompactSupport
      (HasCompactSupport.of_support_subset_isCompact isCompact_scaledStdSimplex
        (subset_trans (subset_tsupport F₁) hsupp))
  have hdist : dist (hmem₁.toLp F₁) f < min δr δI := by
    rw [dist_toLp_eq_eLpNorm]; exact hclose
  refine ⟨F₁, hCD, hsupp, hmem₁, ?_, hδr (lt_of_lt_of_le hdist (min_le_left _ _))⟩
  have := hδI (lt_of_lt_of_le hdist (min_le_right _ _))
  rw [Real.dist_eq, abs_lt] at this
  linarith [this.1]

end PrimeGaps

namespace PrimeGaps
open PropM105

/-- There is a smooth simplex-supported function satisfying the variational inequality determined
by `ρ = θ * M k / 2 - ε`. -/
@[pg_tag "bg246" "lem_choose_rho"]
theorem maynard_smooth_witness_ineq (k : ℕ) (hk : 2 ≤ k) (θ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (ε : ℝ) (hε : 0 < ε)
    (ρ : ℝ) (hρ : ρ = θ * PrimeGaps.M k / 2 - ε) :
    ∃ F : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
      tsupport F ⊆ 𝓡 k ∧ ∃ hmem : MemLp F 2 (volume.restrict (𝓡 k)),
        0 < ‖hmem.toLp F‖ ^ 2 ∧ ∃ δ : ℝ, 0 < δ ∧ ρ * ‖hmem.toLp F‖ ^ 2 <
            (θ / 2 - δ) * (∑ m, PrimeGaps.J m (hmem.toLp F)) := by
  have hMpos : 0 < PrimeGaps.M k := M_pos_of_ne_zero (by omega)
  obtain ⟨hθ0, hθ1⟩ := hθ
  set M : ℝ := PrimeGaps.M k with hM
  set t : ℝ := max 0 (M - ε / θ) with ht
  have htnonneg : 0 ≤ t := le_max_left _ _
  have htltM : t < M := by
    rw [ht]; refine max_lt hMpos ?_
    have : 0 < ε / θ := by positivity
    linarith
  have hlt : (t + M) / 2 < ⨆ f : Lp ℝ 2 (volume.restrict (𝓡 k)),
      (∑ m, PrimeGaps.J m f) / ‖f‖ ^ 2 := by
    change (t + M) / 2 < PrimeGaps.M k; rw [← hM]; linarith
  obtain ⟨f₀, hf₀⟩ := exists_lt_of_lt_ciSup hlt
  have hIf₀ : 0 < ‖f₀‖ ^ 2 := by
    have hInn : 0 ≤ ‖f₀‖ ^ 2 := sq_nonneg _
    refine hInn.lt_of_ne fun h ↦ ?_
    rw [← h, div_zero] at hf₀; linarith [htnonneg]
  obtain ⟨F, hCD, hsupp, hmem, hIpos, hclose⟩ :=
    exists_smooth_ratio_close k hk f₀ hIf₀ (η := (M - t) / 2) (by linarith)
  refine ⟨F, hCD, hsupp, hmem, hIpos, ?_⟩
  set g := hmem.toLp F with hg
  set Q : ℝ := (∑ m, PrimeGaps.J m g) / ‖g‖ ^ 2 with hQ
  have htQ : t < Q := by
    rw [abs_lt] at hclose
    have hbridge : rayleigh k g = Q := rfl
    have hf₀' : (t + M) / 2 < rayleigh k f₀ := hf₀
    unfold rayleigh at * ; linarith [hclose.1]
  have hQpos : 0 < Q := lt_of_le_of_lt htnonneg htQ
  have hJeqQI : ∑ m, PrimeGaps.J m g = Q * ‖g‖ ^ 2 := by
    rw [hQ]
    exact (div_mul_cancel₀ _ (ne_of_gt hIpos)).symm
  refine ⟨ε / (2 * Q), by positivity, ?_⟩
  rw [hJeqQI, hρ]
  have key : θ * M / 2 - ε < (θ / 2 - ε / (2 * Q)) * Q := by
    have hQlt : θ * (M - Q) / 2 < ε / 2 := by
      have h1 : M - Q < ε / θ := by
        have h2 : M - ε / θ ≤ t := le_max_right _ _
        linarith [htQ]
      have : θ * (M - Q) < ε :=
        calc θ * (M - Q) < θ * (ε / θ) := by apply mul_lt_mul_of_pos_left h1 hθ0
          _ = ε := by field_simp
      linarith
    have hexpand : (θ / 2 - ε / (2 * Q)) * Q = θ * Q / 2 - ε / 2 := by
      field_simp [hQpos.ne']
    rw [hexpand]; nlinarith [hQlt]
  calc (θ * M / 2 - ε) * ‖g‖ ^ 2
      < ((θ / 2 - ε / (2 * Q)) * Q) * ‖g‖ ^ 2 := mul_lt_mul_of_pos_right key hIpos
    _ = (θ / 2 - ε / (2 * Q)) * (Q * ‖g‖ ^ 2) := by ring

end PrimeGaps

namespace PrimeGaps
open PropM105

/-- The constant `M k` is positive and at most `k`, and its Rayleigh quotient is approximated from
below by smooth simplex-supported functions. -/
@[pg_tag "bg246" "lem_Mk_approx"]
theorem M_pos_and_le_and_exists_smooth_lt_sum_J (k : ℕ) (hk : 2 ≤ k) :
    (0 < PrimeGaps.M k ∧ PrimeGaps.M k ≤ (k : ℝ)) ∧
    ∀ δ : ℝ, 0 < δ → ∃ F : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F ∧
        tsupport F ⊆ 𝓡 k ∧ ∃ hmem : MemLp F 2 (volume.restrict (𝓡 k)),
          (PrimeGaps.M k - δ) * ‖hmem.toLp F‖ ^ 2 < ∑ m, PrimeGaps.J m (hmem.toLp F) ∧
          0 < ‖hmem.toLp F‖ ^ 2 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
  refine ⟨⟨M_pos n, by exact_mod_cast M_le_k n⟩, ?_⟩
  intro δ hδ
  set k := n + 1
  have hMpos : 0 < PrimeGaps.M k := M_pos n
  have hlt : max (PrimeGaps.M k - δ / 2) (PrimeGaps.M k / 2) <
      ⨆ f : Lp ℝ 2 (volume.restrict (𝓡 k)), (∑ m, PrimeGaps.J m f) / ‖f‖ ^ 2 := by
    change max (PrimeGaps.M k - δ / 2) (PrimeGaps.M k / 2) < PrimeGaps.M k
    exact max_lt (by linarith) (by linarith)
  obtain ⟨f, hf⟩ := exists_lt_of_lt_ciSup hlt
  have hIpos : 0 < ‖f‖ ^ 2 := by
    rcases (sq_nonneg ‖f‖).lt_or_eq with h | h
    · exact h
    · rw [h.symm, div_zero] at hf
      linarith [lt_of_le_of_lt (le_max_right _ _) hf]
  obtain ⟨F, hCD, hsupp, hmem, hIF, hclose⟩ :=
    exists_smooth_ratio_close k hk f hIpos (η := δ / 2) (by linarith)
  refine ⟨F, hCD, hsupp, hmem, ?_, hIF⟩
  rw [abs_lt] at hclose
  have hRF : PrimeGaps.M k - δ < rayleigh k (hmem.toLp F) := by
    have := hclose.1; have := lt_of_le_of_lt (le_max_left _ _) hf
    unfold rayleigh at * ; linarith
  have h := mul_lt_mul_of_pos_right hRF hIF
  rwa [rayleigh, div_mul_cancel₀ _ (ne_of_gt hIF)] at h

end PrimeGaps
