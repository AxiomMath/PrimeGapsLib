/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.S1.FromY
public import PrimeGapsTheory.Sieve.Transforms.YmSubstituteSmooth

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Substituting the smooth first-moment weight

Evaluates the transformed weight sum associated with a smooth simplex-supported function.

## Main results

* `lem_S1_substitute_smooth_y`: Substitutes the smooth weight into the first-moment sum.
-/

@[expose] public section

namespace PrimeGaps

open GPYSieveS1 PrimeGaps.LemS1RestrictSij MaynardSmoothY in
/-- The inner-sum rewrite: the `PrimeGaps.lToY` -guarded tsum produced by `lem_S1_from_y` (guard
`(∀ i, 1 ≤ uᵢ) ∧ RA u`, summand `PrimeGaps.lToY (⇑l₀) u ^ 2 /
  ∏φ`) equals the target's `F²` -guarded tsum
(guard additionally `Squarefree (∏u) ∧ (∏u).Coprime W`, summand
`F(toLp(log u / log R))² / ∏φ`).
-/
theorem subgoal_A {k : ℕ} (hk : 2 ≤ k) (R : ℝ) (W : ℕ) (hR : 0 < R)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ 𝓡 k) :
    (∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) then
          PrimeGaps.lToY (l₀ R W (fun x ↦ F (WithLp.toLp 2 x))) u ^ 2 /
            ∏ i, ((u i).totient : ℝ) else 0) = (∑' u : Fin k → ℕ,
        if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) ∧
              Squarefree (∏ i, u i) ∧ (∏ i, u i).Coprime W then
          (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log R)) ^ 2 /
            (∏ i, (Nat.totient (u i) : ℝ))) else 0) := by
  refine tsum_congr fun u ↦ ?_
  rw [y_from_lambda (W := W) F hk hR hF hFsupp u]
  by_cases hg1 : (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1)
  · by_cases hg2 : Squarefree (∏ i, u i) ∧ (∏ i, u i).Coprime W
    · rw [if_pos hg1, if_pos hg2, if_pos ⟨hg1.1, hg1.2, hg2.1, hg2.2⟩]
    · rw [if_pos hg1, if_neg hg2, if_neg (by tauto)]
      simp
  · rw [if_neg hg1, if_neg (by tauto)]

open GPYSieveS1 PrimeGaps.LemS1RestrictSij MaynardSmoothY in
/-- The sup-norm bound `(PrimeGaps.lToY (l₀ R W (F ∘ toLp))).maxRealAbs ≤ Fmax F`. -/
theorem subgoal_B1 {k : ℕ} (hk : 2 ≤ k) (R : ℝ) (W : ℕ) (hR : 0 < R)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ 𝓡 k) :
    Finsupp.maxRealAbs (PrimeGaps.lToY (l₀ R W (fun x ↦
      F (WithLp.toLp 2 x)))) ≤ Fmax F :=
  maxRealAbs_lambda0_le_Fmax R W F hk hR hF hFsupp

open GPYSieveS1 PrimeGaps.LemS1RestrictSij MaynardSmoothY in
/-- Nonnegativity of the error multiplier
`φ(W) ^ k · N · (log R) ^ k / (W ^ (k + 1) · D₀ N)`, which
lets us replace `Finsupp.maxRealAbs (PrimeGaps.lToY l₀)^2` by the larger
`(Fmax F)^2` in the bound.
-/
theorem subgoal_B2 {k N : ℕ} (R : ℝ) (W : ℕ)
    (hlogR : 0 ≤ Real.log R) (hD0 : 0 ≤ PrimeGaps.D₀ (N : ℝ)) :
    (0 : ℝ) ≤ (Nat.totient W : ℝ) ^ k * N * (Real.log R) ^ k /
        ((W : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) :=
  div_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hlogR k))
    (mul_nonneg (by positivity) hD0)

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
open GPYSieveS1 PrimeGaps.LemS1RestrictSij MaynardSmoothY Real in
/-- For an admissible tuple `h` and a smooth `F` supported in the simplex `𝓡 k`, substituting the
smooth weight
`λ₀ = l₀ (R)
        (W N) (F ∘ toLp)`
into the `S₁` sum: for `θ ∈ (0, 1)` with level of
distribution `1` and `δ ∈ (0, θ/2)`, the sum differs from the `F²` -weighted `u` -sum by an error
of order `C · Fmax(F)² · φ(W)^k · N · (log R)^k / (W^{k+1} · D₀)`.
-/
@[pg_tag "bg246" "lem_S1_substitute_smooth_y"]
theorem lem_S1_substitute_smooth_y {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ 𝓡 k) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∀ v0 : ℕ, V0Valid h (W N) v0 →
      |S1 h (l₀ (R) (W N) (fun x ↦
        F (WithLp.toLp 2 x))) N (W N) v0 - (N / (W N : ℝ)) * (∑' u : Fin k → ℕ,
                if (∀ i, 1 ≤ u i) ∧ RestrictedCoprime u (fun _ _ ↦ 1) ∧
                      Squarefree (∏ i, u i) ∧ (∏ i, u i).Coprime (W N) then
                  (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log (R)))) ^ 2 /
                    (∏ i, (Nat.totient (u i) : ℝ)) else 0)| ≤
        C * (Fmax F) ^ 2 * (Nat.totient (W N) : ℝ) ^ k * N * (Real.log (R)) ^ k /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  intro θ δ hθ hδ
  obtain ⟨C, hC, N₀, hbound⟩ := lem_S1_from_y hk h hadm θ δ hθ hδ
  refine ⟨C, hC, max N₀ (rexp (rexp 1) + 1), ?_⟩
  intro N hN v0 hv0
  have hN₀ : N₀ ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hNexp : rexp (rexp 1) < (N : ℝ) := by
    linarith [le_trans (le_max_right N₀ (rexp (rexp 1) + 1)) hN]
  have hNpos : 0 < N := by
    exact_mod_cast lt_trans (show (0 : ℝ) < rexp (rexp 1) by positivity) hNexp
  set l : (Fin k → ℕ) →₀ ℝ := l₀ (R) (W N) (fun x ↦ F (WithLp.toLp 2 x)) with hl_def
  have hLSfloor : l.HasPermissibleSupport ⌊R⌋₊ (W N) := hasPermissibleSupport_l₀
  have hRpos : 0 < R :=
    Real.rpow_pos_of_pos (by exact_mod_cast hNpos) _
  have H := hbound N hN₀ l hLSfloor v0 hv0
  rw [subgoal_A hk (R) (W N)
    hRpos F hF hFsupp] at H
  refine le_trans H ?_
  have hyMax_le : Finsupp.maxRealAbs (PrimeGaps.lToY l) ≤ Fmax F := subgoal_B1 hk (R) (W N)
      hRpos F hF hFsupp
  have hsq : Finsupp.maxRealAbs (PrimeGaps.lToY l) ^ 2 ≤ (Fmax F) ^ 2 :=
    pow_le_pow_left₀ Finsupp.maxRealAbs_nonneg hyMax_le 2
  have hlogR : 0 ≤ Real.log R := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
    have hN1 : (1 : ℝ) ≤ N := by
      have he : (1 : ℝ) < rexp (rexp 1) := by
        simpa using Real.exp_lt_exp.mpr (Real.exp_pos 1)
      linarith
    rw [PrimeGaps.sieveTruncation, Real.log_rpow hNr]
    exact mul_nonneg (by linarith [hδ.2]) (Real.log_nonneg hN1)
  have hD0 : 0 ≤ PrimeGaps.D₀ (N : ℝ) := by
    unfold PrimeGaps.D₀
    have hNr : (0 : ℝ) < N := by positivity
    have h1 : rexp 1 < Real.log N := (Real.lt_log_iff_exp_lt hNr).mpr hNexp
    have h1pos : 0 < Real.log N := lt_trans (by positivity) h1
    have h2 : (1 : ℝ) < Real.log (Real.log N) := by
      simpa using (Real.lt_log_iff_exp_lt h1pos).mpr h1
    exact (Real.log_pos h2).le
  have hM : (0 : ℝ) ≤ (Nat.totient (W N) : ℝ) ^ k * N * (Real.log (R)) ^ k /
        ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) :=
    subgoal_B2 (k := k) R (W N) hlogR hD0
  have hgroup : ∀ y : ℝ, C * y * (Nat.totient (W N) : ℝ) ^ k * N * (Real.log (R)) ^ k /
        ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) =
      (C * ((Nat.totient (W N) : ℝ) ^ k * N * (Real.log (R)) ^ k /
          ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)))) * y := fun y ↦ by ring
  rw [hgroup, hgroup]
  exact mul_le_mul_of_nonneg_left hsq (mul_nonneg hC.le hM)

end PrimeGaps
