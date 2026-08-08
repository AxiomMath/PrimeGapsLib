/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.Cutoff


/-!
# Second-moment error absorption

Large-parameter estimates that absorb transformed-weight errors into the second-moment scale.
-/

@[expose] public section

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY PrimeGaps
open scoped PrimeGaps PrimeGaps.sieveTruncation PrimeGaps.sieveModulus

namespace Gaps246


/-- Pointwise assembly of the three normalized `fromYm` errors and the
three exactly normalized inverse-form errors. -/
theorem correctedCrossNativeError_le {k N : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) (m : Fin k) (δ θ ε : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (C C₀ C₁ C₂ Cy₀ Cy₁₂ K_W : ℝ)
    (hC : 0 < C)
    (hCy₀ : 0 ≤ Cy₀) (hCy₁₂ : 0 ≤ Cy₁₂)
    (hKW : 0 < K_W)
    (hε : 0 ≤ ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hlogN : 1 ≤ Real.log N)
    (hD0 : 0 < PrimeGaps.D₀ (N : ℝ))
    (hW : 1 ≤ (W N : ℝ))
    (hWa : (W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ) ≤ K_W * Real.log N ^ (2 * k + 3))
    (hU₀ : (⨆ r, |PrimeGaps.ym m
        (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) r|) ≤ Cy₀ *
          MaynardSmoothY.Fmax (Grescale ε F) *
          ((W N).totient : ℝ) *
          Real.log (R ^ (1 + ε)) /
          (W N : ℝ))
    (hU₁ : (⨆ r, |PrimeGaps.ym m
        (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x)))) r|) ≤ Cy₁₂ * MaynardSmoothY.Fmax (Grescale ε F) *
          ((W N).totient : ℝ) *
          Real.log (R ^ (1 + ε)) /
          (W N : ℝ))
    (hU₂ : (⨆ r, |PrimeGaps.ym m
        (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x)))) r|) ≤ Cy₁₂ * MaynardSmoothY.Fmax (Grescale ε F) *
          ((W N).totient : ℝ) *
          Real.log (R ^ (1 + ε)) /
          (W N : ℝ))
    (hY₀ : (PrimeGaps.lToY
        (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))).maxRealAbs ≤
          MaynardSmoothY.Fmax (Grescale ε F))
    (hY₁ : (PrimeGaps.lToY (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F))
    (hY₂ : (PrimeGaps.lToY (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F)) :
    PrimeGaps.correctedCrossNativeError m (9 * k + 3) C C₀ C₁ C₂ N (W N) (R ^ (1 + ε))
      (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
      (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
      (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x))))
      (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x)))) ≤
      (C * Cy₀ ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k +
          C * Cy₁₂ ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k +
          C * Cy₁₂ ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k +
          (C₀ + C₁ + C₂) * (1 + ε) ^ (k + 1) * (θ / 2 - δ)) *
        PrimeGaps.secondMomentErrorScale k N R (W N)
          (MaynardSmoothY.Fmax (Grescale ε F)) := by
  let Fm := MaynardSmoothY.Fmax (Grescale ε F)
  let L : ℝ := Real.log N
  let logRp := Real.log (R ^ (1 + ε))
  let D0 := PrimeGaps.D₀ (N : ℝ)
  let c := θ / 2 - δ
  let q := 1 + ε
  let S := PrimeGaps.secondMomentErrorScale k N R (W N) (MaynardSmoothY.Fmax (Grescale ε F))
  have hc : 0 < c := by dsimp [c]; linarith [hδ.2]
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hFm : 0 ≤ Fm := by
    dsimp [Fm]
    exact MaynardSmoothY.Fmax_nonneg _ hG
  have hφW : 1 ≤ ((W N).totient : ℝ) := PrimeGaps.one_le_totient_W
  have hNr : 0 ≤ (N : ℝ) := by positivity
  have hlogRp : logRp = q * Real.log R := by
    dsimp [logRp, q]
    exact Real.log_rpow (by positivity) _
  have hlogR : Real.log R = c * L := log_sieveTruncation N hN δ θ
  have hlogRp0 : 0 ≤ logRp := by rw [hlogRp, hlogR]; positivity
  have hS : S = Fm ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k /
        ((W N : ℝ) ^ (k + 1) * D0) := by
    simp [S, PrimeGaps.secondMomentErrorScale, Fm, D0]
  let L₀ := PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))
  let L₁ := retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
    Grescale ε F (WithLp.toLp 2 x)))
  let L₂ := discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
    Grescale ε F (WithLp.toLp 2 x)))
  have one (Lx : (Fin k → ℕ) →₀ ℝ) (Cy : ℝ) (hCy : 0 ≤ Cy)
      (hU : (⨆ r, |PrimeGaps.ym m Lx r|) ≤ Cy * Fm * ((W N).totient : ℝ) * logRp / (W N : ℝ))
      (hY : (PrimeGaps.lToY Lx).maxRealAbs ≤ Fm) :
      PrimeGaps.fromYmError m (9 * k + 3) C N (W N) Lx ≤ (C * Cy ^ 2 * q ^ 2 / c ^ (k - 2) +
            C * K_W / c ^ k) * S := by
    change PrimeGaps.fromYmErrorScale (9 * k + 3) C N (W N)
      (⨆ r, |PrimeGaps.ym m Lx r|) (PrimeGaps.lToY Lx).maxRealAbs ≤ _
    simpa [PrimeGaps.fromYmErrorScale, PrimeGaps.weightedDiagonalErrorScale, Fm, L, logRp, D0] using
      PrimeGaps.cross_fromYm_error_absorb hk C Cy (⨆ r, |PrimeGaps.ym m Lx r|)
        (PrimeGaps.lToY Lx).maxRealAbs q c Fm ((W N).totient : ℝ) (W N : ℝ) (N : ℝ)
        L (Real.log R) logRp D0 K_W S hC hCy
        (Real.iSup_nonneg fun _ ↦ abs_nonneg _) hU
        Finsupp.maxRealAbs_nonneg hY hFm hφW hW hlogN hlogRp0
        hD0 hc hKW hNr hlogRp hlogR hWa hS
  have e0 := one L₀ Cy₀ hCy₀ (by simpa [L₀, Fm, logRp] using hU₀)
    (by simpa [L₀, Fm] using hY₀)
  have e1 := one L₁ Cy₁₂ hCy₁₂ (by simpa [L₁, Fm, logRp] using hU₁)
    (by simpa [L₁, Fm] using hY₁)
  have e2 := one L₂ Cy₁₂ hCy₁₂ (by simpa [L₂, Fm, logRp] using hU₂)
    (by simpa [L₂, Fm] using hY₂)
  have inv (Ci : ℝ) : (N : ℝ) / (((W N).totient : ℝ) * L) *
        PrimeGaps.inverseDiagonalApproxErrorScale k Ci (R ^ (1 + ε)) (W N) Fm D0 =
        Ci * q ^ (k + 1) * c * S := by
    rw [PrimeGaps.inverseDiagonalApproxErrorScale]
    exact PrimeGaps.cross_inverse_error_eq Ci q c Fm ((W N).totient : ℝ) (W N : ℝ) (N : ℝ) L
      (Real.log R)
      (Real.log (R ^ (1 + ε))) D0
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hφW))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hW))
      (ne_of_gt (lt_of_lt_of_le zero_lt_one hlogN)) hD0.ne'
      (by dsimp [q]; exact Real.log_rpow (by positivity) _)
      hlogR
  have i0 := inv C₀
  have i1 := inv C₁
  have i2 := inv C₂
  unfold PrimeGaps.correctedCrossNativeError
  dsimp only
  rw [show ((N : ℝ) / (((W N).totient : ℝ) * Real.log N)) =
      (N : ℝ) / (((W N).totient : ℝ) * L) by rfl]
  dsimp [L₀, L₁, L₂] at e0 e1 e2
  have hi : (N : ℝ) / (((W N).totient : ℝ) * L) *
          (PrimeGaps.inverseDiagonalApproxErrorScale k C₀ (R ^ (1 + ε)) (W N) Fm D0 +
            PrimeGaps.inverseDiagonalApproxErrorScale k C₁ (R ^ (1 + ε)) (W N) Fm D0 +
            PrimeGaps.inverseDiagonalApproxErrorScale k C₂ (R ^ (1 + ε)) (W N) Fm D0) =
            (C₀ + C₁ + C₂) * q ^ (k + 1) * c * S := by
    rw [mul_add, mul_add, i0, i1, i2]
    ring
  rw [hi]
  dsimp [q, c, S] at e0 e1 e2 ⊢
  linarith

/-- The weak-room retained error is bounded by a constant multiple of the shared
second-moment error scale. -/
theorem weakFromYmError_le_s2ErrBase {k N : ℕ} (hk : 2 ≤ k) (hN : 1 ≤ N) (m : Fin k) (δ θ ε : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (C Cy K_W : ℝ) (hC : 0 < C) (hCy : 0 ≤ Cy) (hKW : 0 < K_W)
    (hε : 0 ≤ ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hlogN : 1 ≤ Real.log N)
    (hD0 : 0 < PrimeGaps.D₀ (N : ℝ))
    (hW : 1 ≤ (W N : ℝ))
    (hWa : (W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ) ≤ K_W * Real.log N ^ (2 * k + 3))
    (hU : (⨆ r, |PrimeGaps.ym m
        (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x)))) r|) ≤ Cy * MaynardSmoothY.Fmax (Grescale ε F) *
          ((W N).totient : ℝ) * Real.log (R ^ (1 + ε)) / (W N : ℝ)) :
    PrimeGaps.weakFromYmError m (9 * k + 3) C N (W N) (MaynardSmoothY.Fmax (Grescale ε F))
      (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x)))) ≤ (C * Cy ^ 2 * (1 + ε) ^ 2 /
            (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k) *
        PrimeGaps.secondMomentErrorScale k N R (W N)
          (MaynardSmoothY.Fmax (Grescale ε F)) := by
  let Fm := MaynardSmoothY.Fmax (Grescale ε F)
  let L : ℝ := Real.log N
  let logRp := Real.log (R ^ (1 + ε))
  let D0 := PrimeGaps.D₀ (N : ℝ)
  let c := θ / 2 - δ
  let q := 1 + ε
  let S := PrimeGaps.secondMomentErrorScale k N R (W N) (MaynardSmoothY.Fmax (Grescale ε F))
  have hc : 0 < c := by dsimp [c]; linarith [hδ.2]
  have hq : 0 ≤ q := by dsimp [q]; linarith
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hFm : 0 ≤ Fm := by
    dsimp [Fm]
    exact MaynardSmoothY.Fmax_nonneg _ hG
  have hφW : 1 ≤ ((W N).totient : ℝ) := PrimeGaps.one_le_totient_W
  have hNr : 0 ≤ (N : ℝ) := by positivity
  have hlogRp : logRp = q * Real.log R := by
    dsimp [logRp, q]
    exact Real.log_rpow (by positivity) _
  have hlogR : Real.log R = c * L := log_sieveTruncation N hN δ θ
  have hlogRp0 : 0 ≤ logRp := by rw [hlogRp, hlogR]; positivity
  have hS : S = Fm ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k /
        ((W N : ℝ) ^ (k + 1) * D0) := by
    simp [S, PrimeGaps.secondMomentErrorScale, Fm, D0]
  have ht := PrimeGaps.cross_fromYm_error_absorb hk C Cy (⨆ r, |PrimeGaps.ym m
      (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x)))) r|)
    Fm q c Fm ((W N).totient : ℝ) (W N : ℝ) (N : ℝ) L (Real.log R) logRp D0 K_W S
    hC hCy (Real.iSup_nonneg fun _ ↦ abs_nonneg _)
    (by simpa [Fm, logRp] using hU)
    hFm le_rfl hFm hφW hW hlogN hlogRp0 hD0 hc hKW hNr
    hlogRp hlogR hWa hS
  change PrimeGaps.fromYmErrorScale (9 * k + 3) C N (W N)
    (⨆ r, |PrimeGaps.ym m (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 +
      ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) r|) Fm ≤ _
  simpa [PrimeGaps.fromYmErrorScale, PrimeGaps.weightedDiagonalErrorScale,
    Fm, L, logRp, D0, q, c, S]
    using ht

end Gaps246
