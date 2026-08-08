/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.RetainedCRT


/-!
# Inverse diagonal forms

Diagonal inverse forms and their comparison with fixed-width retained profiles.
-/

@[expose] public section

open PrimeGaps
open Finset MeasureTheory GPYSieveS1 MaynardSmoothY
open scoped PrimeGaps

namespace Gaps246

/-- Polarization of the corrected restricted CRT main form at the weak-room
auxiliary parameters. -/
theorem corrected_restrictedCrossSum_polarization {k : ℕ}
    (h : Fin k → ℕ) (hinj : Function.Injective h) (m : Fin k)
    (ε : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (θ δ : ℝ) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
        2 * PrimeGaps.restrictedCrossSum h m (PrimeGaps.sieveModulus N)
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) =
                PrimeGaps.ymWeightedSum m (PrimeGaps.l₀
                  ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
                  (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) -
          PrimeGaps.ymWeightedSum m (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
                ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                  ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) -
                    PrimeGaps.ymWeightedSum m
              (PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
                ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                  ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) := by
  obtain ⟨Ngap, _, hNgap⟩ := PrimeGaps.shiftGap_threshold h
  obtain ⟨Ntwo, _, hNtwo⟩ := PrimeGaps.exists_N0_for_D0_ge_2
  refine ⟨max (max Ngap Ntwo) 1, ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
    exact_mod_cast this
  have hNgapN : Ngap ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNtwoN : Ntwo ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  let L₁ := PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
    ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
      ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
  let L₂ := PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
    ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
      ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
  have hexp : auxTheta δ θ ε / 2 - auxDelta δ θ ε = (θ / 2 - δ) * (1 + ε) := by
    rw [aux_exponent]
    ring
  have hsupp₁ : L₁.HasPermissibleSupport
      ⌊(N : ℝ) ^ (auxTheta δ θ ε / 2 - auxDelta δ θ ε)⌋₊ (PrimeGaps.sieveModulus N) := fun d hd ↦
    epsPermissible_permissibleSupport_of_exponent_eq
      (lambdaRetained_epsPermissible k N δ θ ε m F) hexp
      (Finsupp.mem_support_iff.mp hd)
  have hsupp₂ : L₂.HasPermissibleSupport
      ⌊(N : ℝ) ^ (auxTheta δ θ ε / 2 - auxDelta δ θ ε)⌋₊ (PrimeGaps.sieveModulus N) := fun d hd ↦
    epsPermissible_permissibleSupport_of_exponent_eq
      (lambdaDiscarded_epsPermissible k N δ θ ε m F) hexp
      (Finsupp.mem_support_iff.mp hd)
  have hpol := PrimeGaps.restrictedCrossSum_eq_ym_polarization_finsupp
    h m hinj (auxTheta δ θ ε) (auxDelta δ θ ε) N
    (⇑L₁) (⇑L₂) L₁ L₂ rfl rfl
    hsupp₁ hsupp₂
    (hNgap N hNgapN) (hNtwo N hNtwoN)
  have hadd : L₁ + L₂ = PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
      (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)) :=
    PrimeGaps.retainedL_add_discardedL _ m _
  rwa [hadd] at hpol

open Classical in
theorem inverseDiagonalForm_smoothRetained_le {k N : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N)
    (m : Fin k) (δ θ ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 < η)
    (hR : 1 < PrimeGaps.sieveTruncation N δ θ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε) :
    PrimeGaps.inverseDiagonalForm m (PrimeGaps.sieveModulus N)
        (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
          ε)) (PrimeGaps.sieveModulus N) (fun x ↦
            PrimeGaps.retainedProfile ε η m (Grescale ε F) (WithLp.toLp 2 x.ofLp))) ≤
      PrimeGaps.inverseDiagonalForm m (PrimeGaps.sieveModulus N)
          (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) := by
  have hsmooth := PrimeGaps.summable_inverseDiagonalTerm
    (PrimeGaps.sieveTruncation N (auxDelta δ θ ε) (auxTheta δ θ ε))
    (PrimeGaps.sieveModulus N) m
    (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) (PrimeGaps.sieveModulus N) (fun x ↦
      PrimeGaps.retainedProfile ε η m (Grescale ε F) (WithLp.toLp 2 x.ofLp)))
    (by
      rw [aux_sieveTruncation_eq]
      exact PrimeGaps.hasPermissibleSupport_l₀)
  have hret := PrimeGaps.summable_inverseDiagonalTerm
    (PrimeGaps.sieveTruncation N (auxDelta δ θ ε) (auxTheta δ θ ε))
    (PrimeGaps.sieveModulus N) m
    (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
      ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
        ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
    (by
      rw [aux_sieveTruncation_eq]
      exact PrimeGaps.retainedL_hasPermissibleSupport _ m _ PrimeGaps.hasPermissibleSupport_l₀)
  unfold PrimeGaps.inverseDiagonalForm
  apply hsmooth.tsum_le_tsum _ hret
  intro r
  have hsq : ∀ c y : ℝ, 0 ≤ c → c ≤ 1 → (c * y) ^ 2 ≤ y ^ 2 := by
    intro c y hc0 hc1
    nlinarith [mul_nonneg (mul_nonneg (sub_nonneg.mpr hc1) (by linarith : (0 : ℝ) ≤ 1 + c))
      (sq_nonneg y)]
  unfold PrimeGaps.inverseDiagonalTerm
  by_cases hg : r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (PrimeGaps.sieveModulus N))
  · rw [if_pos hg, if_pos hg, yInverseSum_smoothRetainedAux hk (lt_of_lt_of_le Nat.zero_lt_one hN)
        δ θ ε η hε m F hF hFsupp r,
      PrimeGaps.yInverseSum_retainedL]
    by_cases hc : PrimeGaps.outerProductCutoff ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m r
    · rw [if_pos hc]
      apply div_le_div_of_nonneg_right
        (hsq _ _ (PrimeGaps.retainedRamp_nonneg ε η m _)
          (PrimeGaps.retainedRamp_le_one ε η m _))
      apply Finset.prod_nonneg
      intro i hi
      positivity
    · rw [if_neg hc]
      have hρpos : ∀ i ∈ Finset.univ.erase m, 0 < r i :=
        fun i hi ↦ Nat.zero_lt_of_lt (hg.2 i (Finset.mem_erase.mp hi).1).1
      have hnot := (outerCutoff_iff_aux_logCoord_sum_le_pre
        hN hε hR hρpos).not.mp hc
      have hrzero : PrimeGaps.retainedRamp ε η m (WithLp.toLp 2 (fun i ↦ Real.log (r i : ℝ) /
              Real.log ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)))) = 0 := by
        apply PrimeGaps.retainedRamp_eq_zero_of_boundary hη
        simpa using le_of_not_ge hnot
      rw [hrzero]
      simp
  · rw [if_neg hg, if_neg hg]

/-- The retained inverse form is bounded below by the fixed-width decoupled form. -/
theorem retainedInverse_ge_fixedWidthDecoupled {k : ℕ} (hk : 2 ≤ k)
    (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 < η)
    (m : Fin k) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      PrimeGaps.inverseDiagonalForm m (PrimeGaps.sieveModulus N)
          (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) ≥
                decoupledSum
            ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
            (PrimeGaps.sieveModulus N)
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) m - C * MaynardSmoothY.Fmax
              (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ^ 2 *
            ((PrimeGaps.sieveModulus N).totient : ℝ) ^ (k + 1) *
            Real.log ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) ^ (k + 1) /
            ((PrimeGaps.sieveModulus N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨H, hHadm, hHcard⟩ := PrimeGaps.S2mSmooth.exists_admissible_card k
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  obtain ⟨C, hC, hed⟩ := lem_S2m_expand_drop hk
  obtain ⟨Ne, he⟩ := hed H hHadm hHcard (auxTheta δ θ ε) (auxDelta δ θ ε)
    hΘ hΔ.1 hΔ.2
    (PrimeGaps.retainedProfile ε η m (Grescale ε F))
    (PrimeGaps.retainedProfile_contDiff m (Grescale_contDiff hF))
    (PrimeGaps.retainedProfile_support m (support_rescale_subset hε hFsupp))
  obtain ⟨Nr, hNr⟩ := Filter.eventually_atTop.mp
    (PrimeGaps.R_eventually_ge θ δ hδ.2 2)
  refine ⟨C, hC, max (max Ne (Nr : ℝ)) 1, ?_⟩
  intro N hN
  have hNmax : max Ne (Nr : ℝ) ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNe : Ne ≤ (N : ℝ) := (le_max_left _ _).trans hNmax
  have hNNr : Nr ≤ N := by exact_mod_cast (le_max_right Ne (Nr : ℝ)).trans hNmax
  have hN1 : 1 ≤ N := by exact_mod_cast (le_max_right (max Ne (Nr : ℝ)) 1).trans hN
  have hR : 1 < PrimeGaps.sieveTruncation N δ θ := by linarith [hNr N hNNr]
  have hdom := inverseDiagonalForm_smoothRetained_le
    hk hN1 m δ θ ε η hε hη hR F hF hFsupp
  have herr := he N hNe m
  rw [aux_sieveTruncation_eq] at herr
  have herr' :
      |PrimeGaps.inverseDiagonalForm m (PrimeGaps.sieveModulus N)
            (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦
                PrimeGaps.retainedProfile ε η m (Grescale ε F) (WithLp.toLp 2 x.ofLp))) -
                  decoupledSum
              ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
              (PrimeGaps.sieveModulus N)
              (PrimeGaps.retainedProfile ε η m (Grescale ε F)) m| ≤ C * MaynardSmoothY.Fmax
              (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ^ 2 *
            ((PrimeGaps.sieveModulus N).totient : ℝ) ^ (k + 1) *
            Real.log ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) ^ (k + 1) /
            ((PrimeGaps.sieveModulus N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
    simpa [PrimeGaps.inverseDiagonalForm, PrimeGaps.inverseDiagonalTerm] using herr
  linarith [(abs_le.mp herr').1]

end Gaps246
