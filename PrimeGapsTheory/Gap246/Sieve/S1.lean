/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.Weight
public import PrimeGapsTheory.Gap246.Variational.EnlargedSimplex
public import PrimeGapsTheory.Sieve.S1.Smoothing

/-!
# The ε-enlarged `S₁` asymptotic

This file proves `prop_s1`, the first-moment (`S₁`) asymptotic for the ε-enlarged
sieve weight `lambdaEps`, stated in the error-bound style of the Maynard-600
`lem_S1_smooth`.

## The reduction

Choose auxiliary ordinary truncation parameters whose exponent is
`(1 + ε) * (θ / 2 - δ)`. Their truncation radius is exactly `R ^ (1 + ε)`, and the
enlarged weight is the corresponding ordinary weight `l₀` composed with the linear
rescaling `x ↦ (1 + ε) • x` (`Grescale`). This rescaling absorbs the
`log R → log (R ^ (1 + ε)) = (1 + ε) log R` normalisation change.

Feeding `Grescale ε F` (smooth, supported on `𝓡 k` because `F` is supported on `𝒯_ε`
and scaling by `1/(1+ε)` maps `𝒯_ε` onto `𝓡 k`) into `lem_S1_smooth` therefore
gives the full `S₁` asymptotic for `lambdaEps`.  The only remaining analytic identity is
the **change of variables** `t = (1+ε)u` for the main term integral,
`∫_{𝒯_ε} F² = (1+ε)^k ∫_{𝓡 k} (Grescale ε F)²` (`enlarged_integral_cov`), proved via
the Haar-measure scaling law `Measure.setIntegral_comp_smul_of_pos`.

## Main results

* `prop_s1` — the enlarged `S₁` asymptotic.
-/

@[expose] public section

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY
open scoped PrimeGaps

namespace Gaps246

/-- The `(1+ε)`-rescaled test function `Grescale ε F : x ↦ F ((1+ε)•x)`.  Feeding this into
the un-enlarged machinery recovers the enlarged weight; the rescaling absorbs the change
of the normalising log-truncation from `log R` to `log R' = (1+ε) log R`. -/
noncomputable def Grescale {k : ℕ} (ε : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ) :
    EuclideanSpace ℝ (Fin k) → ℝ := fun x ↦ F ((1 + ε) • x)

/-- The rescaled test function inherits the smoothness of `F`. -/
theorem Grescale_contDiff {k : ℕ} {ε : ℝ} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) :=
  hF.comp (contDiff_const_smul _)

/-! The direct enlarged argument uses auxiliary ordinary truncation parameters whose
exponent is exactly `(1 + ε) * (θ / 2 - δ)`. -/

/-- The auxiliary level `θ'` paired with `auxDelta`, chosen so that
`auxTheta / 2 - auxDelta = (1 + ε) * (θ / 2 - δ)`, i.e. so that the ordinary truncation at
`(θ', δ')` has radius `R ^ (1 + ε)`. -/
noncomputable def auxTheta (δ θ ε : ℝ) : ℝ := 1 / 2 + (1 + ε) * (θ / 2 - δ)

/-- The auxiliary margin `δ'` paired with `auxTheta`, chosen so that
`auxTheta / 2 - auxDelta = (1 + ε) * (θ / 2 - δ)`. -/
noncomputable def auxDelta (δ θ ε : ℝ) : ℝ := 1 / 4 - ((1 + ε) * (θ / 2 - δ)) / 2

theorem aux_params_mem {δ θ ε : ℝ} (hε : 0 ≤ ε) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    auxTheta δ θ ε ∈ Set.Ioo (0 : ℝ) 1 ∧
      auxDelta δ θ ε ∈ Set.Ioo (0 : ℝ) (auxTheta δ θ ε / 2) := by
  have h1ε : 0 < 1 + ε := by linarith
  have hweak : (1 + ε) * θ < 1 := (lt_div_iff₀ hθ.1).mp hεθ
  have hα0 : 0 < (1 + ε) * (θ / 2 - δ) := mul_pos h1ε (sub_pos.mpr hδ.2)
  have hαhalf : (1 + ε) * (θ / 2 - δ) < 1 / 2 := by
    have hle : θ / 2 - δ < θ / 2 := by linarith [hδ.1]
    nlinarith [mul_lt_mul_of_pos_left hle h1ε, hweak]
  unfold auxTheta auxDelta
  constructor <;> constructor <;> linarith

theorem aux_exponent (δ θ ε : ℝ) : auxTheta δ θ ε / 2 - auxDelta δ θ ε = (1 + ε) * (θ / 2 - δ) := by
  unfold auxTheta auxDelta
  ring

/-- The logarithm of the truncation radius, in the truncation exponent. -/
theorem log_sieveTruncation (N : ℕ) (hN : 1 ≤ N) (δ θ : ℝ) :
    Real.log (PrimeGaps.sieveTruncation N δ θ) = (θ / 2 - δ) * Real.log N :=
  Real.log_rpow (by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN) _

/-- The truncation logarithm is nonnegative when the margin stays below half the level. -/
theorem log_sieveTruncation_nonneg (N : ℕ) (hN : 1 ≤ N) {δ θ : ℝ} (hδ : δ < θ / 2) :
    0 ≤ Real.log (PrimeGaps.sieveTruncation N δ θ) := by
  rw [log_sieveTruncation N hN δ θ]
  exact mul_nonneg (by linarith) (Real.log_nonneg (by exact_mod_cast hN))

/-- The auxiliary ordinary truncation is exactly the enlarged truncation. -/
theorem aux_sieveTruncation_eq (N : ℕ) (δ θ ε : ℝ) :
    PrimeGaps.sieveTruncation N (auxDelta δ θ ε) (auxTheta δ θ ε) =
      (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := by
  simp only [PrimeGaps.sieveTruncation, aux_exponent]
  rw [← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  ring

/-- The enlarged weight is an ordinary `l₀` weight at the auxiliary parameters.
The rescaling absorbs the change from `log R` to `log (R ^ (1 + ε))`. -/
theorem lambdaEps_eq_l₀_aux {k N : ℕ} {δ θ ε : ℝ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hN : 1 ≤ N) (hε : 0 ≤ ε) :
    lambdaEps k N δ θ ε F = ⇑(PrimeGaps.l₀
        (PrimeGaps.sieveTruncation N (auxDelta δ θ ε) (auxTheta δ θ ε))
        (PrimeGaps.sieveModulus N)
        (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) := by
  have hne : (1 + ε) ≠ 0 := by positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hN
  have hpos : 0 < PrimeGaps.sieveTruncation N δ θ := Real.rpow_pos_of_pos hNpos _
  have hlog : Real.log (PrimeGaps.sieveTruncation N (auxDelta δ θ ε) (auxTheta δ θ ε)) =
      (1 + ε) * Real.log (PrimeGaps.sieveTruncation N δ θ) := by
    rw [aux_sieveTruncation_eq, Real.log_rpow hpos]
  funext d
  rw [PrimeGaps.l₀_apply]
  unfold lambdaEps Finset.permissibleSupport
  rw [← aux_sieveTruncation_eq]
  congr 1
  · push_cast
    ring
  · apply Finset.sum_congr rfl
    intro r _
    congr 1
    · push_cast
      ring
    · change F (WithLp.toLp 2
              (fun i ↦ Real.log (r i) / Real.log (PrimeGaps.sieveTruncation N δ θ))) =
          Grescale ε F (WithLp.toLp 2 (fun i ↦ Real.log (r i) / Real.log
                (PrimeGaps.sieveTruncation N (auxDelta δ θ ε) (auxTheta δ θ ε))))
      unfold Grescale
      congr 1
      rw [← WithLp.toLp_smul]
      congr 1
      funext i
      rw [Pi.smul_apply, smul_eq_mul, hlog, ← mul_div_assoc, mul_div_mul_left _ _ hne]

open scoped Pointwise in
/-- **Homothety change of variables.** An integral over the corner region of total mass `c` is the
integral of the `c`-rescaled integrand over `𝓡 n`, carrying the Jacobian factor `c ^ n`.

Proved from `c • 𝓡 n = 𝓡(n, c)` and the Haar scaling law
`Measure.setIntegral_comp_smul_of_pos` for the `EuclideanSpace` volume
(Jacobian `c ^ n` via `finrank_euclideanSpace_fin`). -/
theorem setIntegral_scaledStdSimplex {n : ℕ} {c : ℝ} (hc : 0 < c)
    (G : EuclideanSpace ℝ (Fin n) → ℝ) :
    ∫ x in 𝓡(n, c), G x = c ^ n * ∫ x in 𝓡 n, G (c • x) := by
  have hne : (c ^ n) ≠ 0 := by positivity
  have key := MeasureTheory.Measure.setIntegral_comp_smul_of_pos
    (volume : Measure (EuclideanSpace ℝ (Fin n))) G (𝓡 n) hc
  rw [finrank_euclideanSpace_fin, smul_stdSimplex n hc] at key
  rw [key, smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hne, one_mul]

/-- **Change of variables (the residual analytic identity).** The main-term integral over
the ε-enlarged simplex `𝒯_ε` equals `(1+ε)^k` times the integral over `𝓡 k` of the
`(1+ε)`-rescaled integrand.  This is the substitution `t = (1+ε)u`, which maps `𝓡 k`
diffeomorphically onto `𝒯_ε` and multiplies the `k`-dimensional Lebesgue measure by
`(1+ε)^k`.

Proved from `(1+ε) • 𝓡 k = 𝒯_ε` and the Haar scaling law
`Measure.setIntegral_comp_smul_of_pos` for the `EuclideanSpace` volume
(Jacobian `(1+ε)^k` via `finrank_euclideanSpace_fin`). -/
theorem enlarged_integral_cov {k : ℕ} (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) :
    ∫ x in enlargedSimplex k ε, (F x) ^ 2 = (1 + ε) ^ k * ∫ x in 𝓡 k, (Grescale ε F x) ^ 2 :=
  setIntegral_scaledStdSimplex (by linarith) (fun x ↦ (F x) ^ 2)

/-- **Support transfer.** If `F` is supported on `𝒯_ε`, then the `(1+ε)`-rescaled
`Grescale ε F` is supported on `𝓡 k`, because `(1+ε)•x ∈ 𝒯_ε` forces `x ∈ 𝓡 k`. -/
theorem support_rescale_subset {k : ℕ} {ε : ℝ} (hε : 0 ≤ ε)
    {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε) :
    Function.support (Grescale ε F) ⊆ 𝓡 k := by
  have h1ε : 0 < 1 + ε := by linarith
  rw [← enlargedSimplex_zero k]
  intro x hx
  simp only [Grescale, Function.mem_support] at hx
  obtain ⟨hnn, hsum⟩ := hFsupp hx
  have hnn' : ∀ i, 0 ≤ x i := by
    intro i
    have hi := hnn i
    rw [PiLp.smul_apply, smul_eq_mul] at hi
    exact (mul_nonneg_iff_of_pos_left h1ε).mp hi
  have hsum' : (1 + ε) * ∑ i, x i ≤ 1 + ε := by
    rw [Finset.mul_sum]
    refine le_trans (le_of_eq (Finset.sum_congr rfl fun i _ ↦ ?_)) hsum
    rw [PiLp.smul_apply, smul_eq_mul]
  refine ⟨hnn', ?_⟩
  have : ∑ i, x i ≤ 1 := by nlinarith [hsum']
  simpa using this

open PrimeGaps in
/-- **`prop_s1` — the ε-enlarged `S₁` asymptotic.**  For a smooth `F` supported on the
enlarged simplex `𝒯_ε = enlargedSimplex k ε`, the first moment `S₁` of the enlarged weight
`lambdaEps` equals its main term
`φ(W)^k · N · (log R)^k / W^{k+1} · ∫_{𝒯_ε} F²`
(with the *original* `R = sieveTruncation N δ θ`) up to an error of order
`Fmax(Grescale ε F)² · φ(W)^k · N · (log R)^k / (W^{k+1} · D₀)`, for all sufficiently
large `N`.  The extra hypothesis `1+ε < 1/θ` is the enlargement room `(1+ε)θ < 1`;
unlike the stronger reparametrisation condition, it retains the `δ → 0`, `θ → 1/2`
window. -/
theorem prop_s1 {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (ε : ℝ) (hε : 0 ≤ ε) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFsupp : Function.support F ⊆ enlargedSimplex k ε) :
    ∀ θ δ : ℝ, θ ∈ Set.Ioo (0 : ℝ) 1 → δ ∈ Set.Ioo (0 : ℝ) (θ / 2) → 1 + ε < 1 / θ →
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
    ∀ v0 : ℕ, V0Valid h (PrimeGaps.sieveModulus N) v0 →
      |S1 h (lambdaEps k N δ θ ε F) N (PrimeGaps.sieveModulus N) v0 -
          ((PrimeGaps.sieveModulus N).totient : ℝ) ^ k * (N : ℝ) *
              Real.log (PrimeGaps.sieveTruncation N δ θ) ^ k /
              (PrimeGaps.sieveModulus N : ℝ) ^ (k + 1) * (∫ x in enlargedSimplex k ε, (F x) ^ 2)| ≤
        C * (MaynardSmoothY.Fmax (Grescale ε F)) ^ 2 * ((PrimeGaps.sieveModulus N).totient : ℝ) ^
          k * (N : ℝ) * Real.log (PrimeGaps.sieveTruncation N δ θ) ^ k /
            ((PrimeGaps.sieveModulus N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  intro θ δ hθ hδ hεθ
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  -- Re-express the enlarged truncation as `N^(Θ/2-Δ)` with an auxiliary
  -- `0 < Δ < Θ/2`, without tying `Θ` to the distribution exponent.
  obtain ⟨hΘmem, hΔmem⟩ := aux_params_mem hε hθ hδ hεθ
  set Θ : ℝ := auxTheta δ θ ε with hΘ
  set Δ : ℝ := auxDelta δ θ ε with hΔ
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k := support_rescale_subset hε hFsupp
  obtain ⟨C, hCpos, N₀, hbound⟩ := lem_S1_smooth hk h hadm (Grescale ε F) hG hGsupp Θ Δ hΘmem hΔmem
  refine ⟨C * (1 + ε) ^ k, by positivity, max N₀ 1, ?_⟩
  intro N hN v0 hv0
  have hN0 : N₀ ≤ (N : ℝ) := le_trans (le_max_left _ _) hN
  have hN1 : (1 : ℕ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN1)
  have hRaux :
      PrimeGaps.sieveTruncation N Δ Θ =
        (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := aux_sieveTruncation_eq N δ θ ε
  have hlaux : (⇑(PrimeGaps.l₀
          (PrimeGaps.sieveTruncation N Δ Θ) (PrimeGaps.sieveModulus N)
          (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) :
          (Fin k → ℕ) → ℝ) = lambdaEps k N δ θ ε F :=
    (lambdaEps_eq_l₀_aux F hN1 hε).symm
  have hkey := hbound N hN0 v0 hv0
  rw [hlaux] at hkey
  have hlogaux : Real.log (PrimeGaps.sieveTruncation N Δ Θ) =
        (1 + ε) * Real.log (PrimeGaps.sieveTruncation N δ θ) := by
    rw [hRaux, Real.log_rpow (Real.rpow_pos_of_pos hNpos _)]
  rw [hlogaux] at hkey
  rw [enlarged_integral_cov ε hε F]
  set lr : ℝ := Real.log (PrimeGaps.sieveTruncation N δ θ) with hlrdef
  set Wc : ℝ := (PrimeGaps.sieveModulus N : ℝ) with hWcdef
  set phi : ℝ := ((PrimeGaps.sieveModulus N).totient : ℝ) with hphidef
  set D0 : ℝ := PrimeGaps.D₀ (N : ℝ) with hD0def
  set Ik : ℝ := ∫ x in 𝓡 k, (Grescale ε F x) ^ 2 with hIkdef
  set Fm : ℝ := (MaynardSmoothY.Fmax (Grescale ε F)) ^ 2 with hFmdef
  have hmain : phi ^ k * (N : ℝ) * ((1 + ε) * lr) ^ k / Wc ^ (k + 1) * Ik =
        phi ^ k * (N : ℝ) * lr ^ k / Wc ^ (k + 1) * ((1 + ε) ^ k * Ik) := by
    rw [mul_pow]; ring
  have herr : C * Fm * phi ^ k * (N : ℝ) * ((1 + ε) * lr) ^ k / (Wc ^ (k + 1) * D0) =
        C * (1 + ε) ^ k * Fm * phi ^ k * (N : ℝ) * lr ^ k / (Wc ^ (k + 1) * D0) := by
    rw [mul_pow]; ring
  rw [hmain, herr] at hkey
  exact hkey

end Gaps246
