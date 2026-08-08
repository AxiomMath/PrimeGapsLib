/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Transforms.YFromLambda
public import PrimeGapsTheory.Sieve.Transforms.YmFromY

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Smooth distinguished transformed weights

Evaluates the distinguished transform for smooth Maynard sieve weights.

## Main results

* `exists_abs_ym_sub_yInverseSum_le`: Bounds the difference between the distinguished
  transform and its inverse sum.
-/

@[expose] public section

open scoped ENNReal
open scoped Finset

namespace MaynardSmoothY

open scoped BigOperators PrimeGaps
open ArithmeticFunction (moebius)

/-- The norm constant associated to the test function `F: EuclideanSpace ℝ (Fin k) → ℝ`:
`Fmax:= sup over t in [0,1]^k of ( |F t| + sum_i |partial_i F t| )`, where the partial
derivative in the `i` -th coordinate is `fderiv ℝ F t (EuclideanSpace.single i 1)`. -/
noncomputable def Fmax {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) : ℝ :=
  sSup ((fun t : EuclideanSpace ℝ (Fin k) ↦
      |F t| + ∑ i : Fin k, |fderiv ℝ F t (EuclideanSpace.single i 1)|) ''
    {t : EuclideanSpace ℝ (Fin k) | ∀ i, t i ∈ Set.Icc (0 : ℝ) 1})

/-- The reference error size `Fmax * phi(W) * log R / (W * D_0)` at a natural scale parameter `N`.
-/
noncomputable def errorSize {k : ℕ} (R : ℝ) (W : ℕ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (N : ℕ) : ℝ :=
  Fmax F * (W.totient : ℝ) * Real.log R / ((W : ℝ) * PrimeGaps.D₀ N)

/-- For smooth `F`, the function `t ↦ |F t| + ∑ᵢ |∂ᵢ F t|` is bounded above on `[0,1]^k`. -/
theorem abs_F_bddAbove {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F) :
    BddAbove ((fun t : EuclideanSpace ℝ (Fin k) ↦
        |F t| + ∑ i : Fin k, |fderiv ℝ F t (EuclideanSpace.single i 1)|) ''
      {t : EuclideanSpace ℝ (Fin k) | ∀ i, t i ∈ Set.Icc (0 : ℝ) 1}) := by
  have hcube : IsCompact (Set.univ.pi (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ ↦ isCompact_Icc)
  have hsetEq : {t : EuclideanSpace ℝ (Fin k) | ∀ i, t i ∈ Set.Icc (0 : ℝ) 1} =
      WithLp.toLp 2 '' (Set.univ.pi (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1)) := by
    ext t
    constructor
    · intro ht
      refine ⟨t.ofLp, ?_, ?_⟩
      · intro i _; exact ht i
      · apply WithLp.toLp_ofLp
    · rintro ⟨x, hx, rfl⟩
      intro i; exact hx i (Set.mem_univ _)
  have hcomp : IsCompact {t : EuclideanSpace ℝ (Fin k) | ∀ i, t i ∈ Set.Icc (0 : ℝ) 1} := by
    rw [hsetEq]
    exact hcube.image (PiLp.continuous_toLp (p := (2 : ℝ≥0∞)) (β := fun _ : Fin k ↦ ℝ))
  have hcf : Continuous (fderiv ℝ F) := hFsmooth.continuous_fderiv (by simp)
  have hcont : Continuous (fun t : EuclideanSpace ℝ (Fin k) ↦
      |F t| + ∑ i : Fin k, |fderiv ℝ F t (EuclideanSpace.single i 1)|) := by
    refine (hFsmooth.continuous.abs).add ?_
    refine continuous_finsetSum _ (fun i _ ↦ ?_)
    exact (hcf.clm_apply continuous_const).abs
  exact (hcomp.image hcont).bddAbove

/-- `|F x| ≤ Fmax F` at every point of the cube `[0,1]^k`, for smooth `F`. -/
theorem abs_F_le_Fmax {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) {x : EuclideanSpace ℝ (Fin k)}
    (hx : ∀ i, x.ofLp i ∈ Set.Icc (0 : ℝ) 1) :
    |F x| ≤ Fmax F := by
  have hle : |F x| + ∑ i, |(fderiv ℝ F x) (EuclideanSpace.single i 1)| ≤ Fmax F :=
    le_csSup (abs_F_bddAbove F hF) ⟨x, hx, rfl⟩
  have hnn : (0 : ℝ) ≤ ∑ i, |(fderiv ℝ F x) (EuclideanSpace.single i 1)| :=
    Finset.sum_nonneg fun i _ ↦ abs_nonneg _
  linarith

/-- `0 ≤ Fmax F` for smooth `F`. -/
theorem Fmax_nonneg {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ) (hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F) :
    0 ≤ Fmax F := by
  have hbdd := abs_F_bddAbove F hFsmooth
  unfold Fmax
  have hmem : |F (0 : EuclideanSpace ℝ (Fin k))| +
      ∑ i : Fin k, |fderiv ℝ F (0 : EuclideanSpace ℝ (Fin k)) (EuclideanSpace.single i 1)| ∈
      ((fun t : EuclideanSpace ℝ (Fin k) ↦
          |F t| + ∑ i : Fin k, |fderiv ℝ F t (EuclideanSpace.single i 1)|) ''
        {t : EuclideanSpace ℝ (Fin k) | ∀ i, t i ∈ Set.Icc (0 : ℝ) 1}) :=
    ⟨0, fun _ ↦ ⟨le_refl 0, zero_le_one⟩, rfl⟩
  have h1 := le_csSup hbdd hmem
  have h2 : (0 : ℝ) ≤ |F (0 : EuclideanSpace ℝ (Fin k))| +
      ∑ i : Fin k, |fderiv ℝ F (0 : EuclideanSpace ℝ (Fin k))
        (EuclideanSpace.single i 1)| := by
    have hs := Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) ↦
      abs_nonneg (fderiv ℝ F (0 : EuclideanSpace ℝ (Fin k)) (EuclideanSpace.single i 1)))
    have ha := abs_nonneg (F (0 : EuclideanSpace ℝ (Fin k)))
    positivity
  linarith

open PrimeGaps Finset in
/-- `lToY (l₀ R W F) r = F (fun i ↦ log (r i) / log R)` when `∏ i, r i` is squarefree and coprime
to `W`, and `0` otherwise. -/
theorem y_from_lambda_smooth {k : ℕ} (R : ℝ) (W : ℕ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hk : 2 ≤ k) (hR : 0 < R) (hF_cont : Continuous F)
    (hF_supp : Function.support F ⊆ 𝓡 k) (r : Fin k → ℕ) :
    lToY (l₀ R W (fun x ↦ F (WithLp.toLp 2 x))) r =
      if Squarefree (∏ i, r i) ∧ (∏ i, r i).Coprime W then
        F (WithLp.toLp 2 (fun i ↦ Real.log (r i) / Real.log R))
      else 0 :=
  lToY_l₀_apply F (by omega) hR hF_cont hF_supp r

/-- `|lToY (l₀ R W F) s| ≤ Fmax F`, the log-scaled arguments lying in the unit cube. -/
theorem abs_lToY_lambda0_le_Fmax (R : ℝ) (W : ℕ) {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hk : 2 ≤ k) (hR : 0 < R) (hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ 𝓡 k) (s : Fin k → ℕ) :
    |PrimeGaps.lToY (PrimeGaps.l₀ R W (fun x ↦ F (WithLp.toLp 2 x))) s| ≤ Fmax F := by
  have hFnn : 0 ≤ Fmax F := Fmax_nonneg F hFsmooth
  have hbdd := abs_F_bddAbove F hFsmooth
  have hFbound : ∀ x : EuclideanSpace ℝ (Fin k), (∀ i, x i ∈ Set.Icc (0 : ℝ) 1) → |F x| ≤
    Fmax F := by
    intro x hx
    have hmem : |F x| + ∑ i : Fin k, |fderiv ℝ F x (EuclideanSpace.single i 1)| ∈
        ((fun t : EuclideanSpace ℝ (Fin k) ↦
          |F t| + ∑ i : Fin k, |fderiv ℝ F t (EuclideanSpace.single i 1)|) ''
          {t : EuclideanSpace ℝ (Fin k) | ∀ i, t i ∈ Set.Icc (0 : ℝ) 1}) := ⟨x, hx, rfl⟩
    have h1 : |F x| + ∑ i : Fin k, |fderiv ℝ F x (EuclideanSpace.single i 1)| ≤ Fmax F :=
      le_csSup hbdd hmem
    have h2 : (0 : ℝ) ≤ ∑ i : Fin k, |fderiv ℝ F x (EuclideanSpace.single i 1)| :=
      Finset.sum_nonneg (fun i _ ↦ abs_nonneg _)
    linarith
  rw [y_from_lambda_smooth R W F hk hR hFsmooth.continuous hFsupp s]
  by_cases hcond : Squarefree (∏ i, s i) ∧ (∏ i, s i).Coprime W
  · rw [if_pos hcond]
    set arg : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2
        (fun i ↦ Real.log (s i) / Real.log R) with harg
    by_cases hsupp : arg ∈ Function.support F
    · exact hFbound arg (PrimeGaps.coord_mem_Icc_of_mem_R (hFsupp hsupp))
    · rw [Function.mem_support, not_not] at hsupp
      rw [hsupp, abs_zero]; exact hFnn
  · rw [if_neg hcond, abs_zero]; exact hFnn

/-- `(lToY (l₀ R W F)).maxRealAbs ≤ Fmax F`, the hypothesis
`exists_abs_ym_sub_yInverseSum_le` requires. -/
theorem maxRealAbs_lambda0_le_Fmax (R : ℝ) (W : ℕ) {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hk : 2 ≤ k) (hR : 0 < R) (hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ 𝓡 k) :
    (PrimeGaps.lToY (PrimeGaps.l₀ R W (fun x ↦
      F (WithLp.toLp 2 x)))).maxRealAbs ≤ Fmax F := by
  rw [Finsupp.maxRealAbs_le_iff]
  intro s
  exact abs_lToY_lambda0_le_Fmax R W F hk hR hFsmooth hFsupp s

open PrimeGaps in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Under a smooth `F` supported on `𝓡 k`, the difference between `ym m l r` and
`yInverseSum l m r` is at most a constant depending on `k` times `errorSize R (W N) F N`,
provided `l` has sieve support and `(PrimeGaps.lToY l).maxRealAbs ≤ Fmax F`. -/
@[pg_tag "bg246" "lem_ym_substitute_smooth"]
theorem exists_abs_ym_sub_yInverseSum_le {k : ℕ} :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (H : Finset ℕ), H.Admissible → #H = k →
      ∀ (θ δ : ℝ), θ ∈ Set.Ioo (0 : ℝ) 1 → 0 < δ → δ < θ / 2 →
      ∀ (F : EuclideanSpace ℝ (Fin k) → ℝ), ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 k →
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (l : (Fin k → ℕ) →₀ ℝ), l.HasPermissibleSupport ⌊R⌋₊ (W N) →
          (PrimeGaps.lToY l).maxRealAbs ≤ Fmax F →
          ∀ (m : Fin k) (r : Fin k → ℕ), r m = 1 → (∀ i, Squarefree (r i)) →
            |(PrimeGaps.ym m l) r - PrimeGaps.yInverseSum l m r| ≤
              C * errorSize R (W N) F N := by
  classical
  obtain ⟨C, hCpos, hcore⟩ := PrimeGaps.maynard_ym_identity (k := k)
  refine ⟨C, hCpos.le, ?_⟩
  intro H hH hcard θ δ hθIoo hδ hδθ F hFsmooth _
  obtain ⟨N₀_id, h_id⟩ := hcore H hH hcard θ δ hθIoo hδ hδθ
  obtain ⟨N₀_thresh, h_thresh⟩ := PrimeGaps.exists_large_N0_for_ym θ δ hδθ
  refine ⟨max N₀_id N₀_thresh, ?_⟩
  intro N hN l hl hyMax_Fmax m r hrm hrsq
  obtain ⟨hD4, _, hlogR_ge_1, _⟩ := h_thresh N (le_trans (le_max_right _ _) hN)
  have hbase := h_id N (le_trans (le_max_left _ _) hN) l hl m r hrm hrsq
  have hFmax_nn : 0 ≤ Fmax F := Fmax_nonneg F hFsmooth
  have hyMax_nn : 0 ≤ (PrimeGaps.lToY l).maxRealAbs := Finsupp.maxRealAbs_nonneg
  have hφWnn : (0 : ℝ) ≤ ((W N).totient : ℝ) := by positivity
  have hlogR_pos : 0 < Real.log R := by linarith
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hD0pos : 0 < PrimeGaps.D₀ N := by linarith
  have hdenom_pos : (0 : ℝ) < (W N : ℝ) * PrimeGaps.D₀ N := mul_pos hWpos hD0pos
  refine le_trans hbase ?_
  have hnum : (PrimeGaps.lToY l).maxRealAbs * ((W N).totient : ℝ) * Real.log R ≤
      Fmax F * ((W N).totient : ℝ) * Real.log R := by
    gcongr
  unfold errorSize
  rw [show C * (Fmax F * ((W N).totient : ℝ) * Real.log R / ((W N : ℝ) * PrimeGaps.D₀ N)) =
      C * (Fmax F * ((W N).totient : ℝ) * Real.log R) / ((W N : ℝ) * PrimeGaps.D₀ N) by ring]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hnum hCpos.le) hdenom_pos.le
end MaynardSmoothY
