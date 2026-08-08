/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.ErrorAbsorption


/-!
# The ε-enlarged second-moment lower bound

The fixed-width retained-square and cross-term estimates, assembled into
`prop_s2_fixedWidth`.
-/

@[expose] public section

open Real

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY PrimeGaps
open scoped PrimeGaps PrimeGaps.sieveTruncation PrimeGaps.sieveModulus

namespace Gaps246

/-- The retained/discarded cross term is negligible. -/
theorem crossTerm_negligible {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (m : Fin k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
      2 * PrimeGaps.bilinearPrimeSum h N m
          (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))) w₀ ≥ - (C *
            PrimeGaps.secondMomentErrorScale k N R (W N)
              (MaynardSmoothY.Fmax (Grescale ε F))) := by
  obtain ⟨Cb, Cd, C₀, C₁, C₂, hCb, hCd, hC₀, hC₁, hC₂, Nc, hc⟩ :=
    corrected_cross_native_weak hk h hadm m ε hε F hF hFsupp
      θ δ hθ hθ' hBV hδ hεθ
  obtain ⟨Cy, hCy, Ny, hy⟩ := corrected_ym_sup_le_weak m hk ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨K_W, hKW, NW, hW⟩ := PrimeGaps.rsq_Wasymp (k := k)
  obtain ⟨Ng, hg⟩ := PrimeGaps.ym_phiW_logR_large δ θ hδ
  let K := 2 * Cb * K_W / (θ / 2 - δ) ^ k + Cd * Cy ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) +
      Cd * K_W / (θ / 2 - δ) ^ k + Cd * Cy ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) +
      Cd * K_W / (θ / 2 - δ) ^ k + Cd * Cy ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) +
      Cd * K_W / (θ / 2 - δ) ^ k + (C₀ + C₁ + C₂) * (1 + ε) ^ (k + 1) * (θ / 2 - δ)
  refine ⟨K + 1, by
    have hcδ : 0 < θ / 2 - δ := by linarith [hδ.2]
    have : 0 ≤ K := by
      dsimp [K]
      positivity
    linarith,
    max Nc (max Ny (max NW (max Ng (rexp 1)))), ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hNc, hNy, hNW, hNg, hNexp⟩ := hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hNexp
    exact_mod_cast this
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
  have hlogN : 1 ≤ Real.log N := by
    have ht := Real.log_le_log (Real.exp_pos 1) hNexp
    rwa [Real.log_exp] at ht
  obtain ⟨hW1, hWa⟩ := hW N hNW
  obtain ⟨hD0, _, _⟩ := hg N hNg
  have hnative := hc N hNc w₀ hw₀
  obtain ⟨hU₀, hU₁, hU₂⟩ := hy N hNy
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k := support_rescale_subset hε hFsupp
  have hY₀ : (PrimeGaps.lToY (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
    Grescale ε F (WithLp.toLp 2 x)))).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F) :=
    maxRealAbs_l₀_le_Fmax hk hNpos δ θ ε hG hGsupp
  have hY₁ : (PrimeGaps.lToY
        (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F) :=
    maxRealAbs_retainedL_le_Fmax hk hNpos δ θ ε m hG hGsupp
  have hY₂ : (PrimeGaps.lToY
        (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F) :=
    maxRealAbs_discardedL_le_Fmax hk hNpos δ θ ε m hG hGsupp
  have hnorm := correctedCrossNativeError_le hk hN1 m δ θ ε F hF
    Cd C₀ C₁ C₂ Cy Cy K_W hCd hCy hCy hKW
    hε hδ hlogN hD0 hW1 hWa
    hU₀ hU₁ hU₂
    hY₀ hY₁ hY₂
  have hlogpos : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hlogN
  have hwd (Lx : (Fin k → ℕ) →₀ ℝ) : PrimeGaps.weightedDiagonalErrorEarly m Cd N (W N) Lx ≤
        PrimeGaps.fromYmError m (9 * k + 3) Cd N (W N) Lx := by
    unfold PrimeGaps.weightedDiagonalErrorEarly PrimeGaps.fromYmError
    have ht : 0 ≤ Cd * (Finsupp.maxRealAbs (PrimeGaps.lToY Lx)) ^ 2 *
        (N : ℝ) / Real.log N ^ (9 * (k : ℝ) + 3) := by
      positivity
    linarith
  have hbridge : PrimeGaps.weakCrossNativeError m (9 * k + 3) Cb Cd C₀ C₁ C₂
          N (W N) (R ^ (1 + ε)) (MaynardSmoothY.Fmax (Grescale ε F))
          (PrimeGaps.D₀ (N : ℝ))
          (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
          (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))
          (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x)))) ≤
          2 * (Cb * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
              (N : ℝ) / Real.log N ^ (9 * (k : ℝ) + 3)) +
            PrimeGaps.correctedCrossNativeError m (9 * k + 3)
              Cd C₀ C₁ C₂ N (W N) (R ^ (1 + ε))
              (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
              (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
              (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x))))
              (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x)))) := by
    unfold PrimeGaps.weakCrossNativeError PrimeGaps.correctedCrossNativeError
    dsimp only
    have h0 := hwd (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
    have h1 := hwd (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
      Grescale ε F (WithLp.toLp 2 x))))
    have h2 := hwd (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
      Grescale ε F (WithLp.toLp 2 x))))
    linarith
  let Fm := MaynardSmoothY.Fmax (Grescale ε F)
  let L : ℝ := Real.log N
  let D0 := PrimeGaps.D₀ (N : ℝ)
  let c := θ / 2 - δ
  let S := PrimeGaps.secondMomentErrorScale k N R (W N) (MaynardSmoothY.Fmax (Grescale ε F))
  have hcpos : 0 < c := by dsimp [c]; linarith [hδ.2]
  have hFm0 : 0 ≤ Fm := by
    dsimp [Fm]
    exact MaynardSmoothY.Fmax_nonneg _ hG
  have hφW1 : 1 ≤ ((W N).totient : ℝ) := PrimeGaps.one_le_totient_W
  have hlogR : Real.log R = c * L := log_sieveTruncation N hN1 δ θ
  have hSform : S = Fm ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k /
        ((W N : ℝ) ^ (k + 1) * D0) := by
    simp [S, PrimeGaps.secondMomentErrorScale, Fm, D0]
  have htail :
      2 * (Cb * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ (9 * (k : ℝ) + 3)) ≤
        (2 * Cb * K_W / (θ / 2 - δ) ^ k) * PrimeGaps.secondMomentErrorScale k N R (W N)
              (MaynardSmoothY.Fmax (Grescale ε F)) := by
    have ht := PrimeGaps.cross_fromYm_tail_absorb hk (2 * Cb) Fm Fm ((W N).totient : ℝ) (W N : ℝ)
        (N : ℝ) L (Real.log R) D0 c K_W S
        (by positivity) hFm0 le_rfl hφW1 hW1 hlogN hD0
        hcpos hKW (by positivity) hlogR hWa hSform
    change 2 * Cb * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
        (N : ℝ) / Real.log N ^ (9 * (k : ℝ) + 3) ≤ (2 * Cb * K_W / (θ / 2 - δ) ^ k) *
          PrimeGaps.secondMomentErrorScale k N R (W N) (MaynardSmoothY.Fmax (Grescale ε F)) at ht
    calc _
        = 2 * Cb * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
            (N : ℝ) / Real.log N ^ (9 * (k : ℝ) + 3) := by ring
      _ ≤ _ := ht
  have habs :
      |2 * PrimeGaps.bilinearPrimeSum h N m
          (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))) w₀| ≤ K *
            PrimeGaps.secondMomentErrorScale k N R (W N)
              (MaynardSmoothY.Fmax (Grescale ε F)) :=
    calc _
        ≤ PrimeGaps.weakCrossNativeError m (9 * k + 3)
            Cb Cd C₀ C₁ C₂ N (W N) (R ^ (1 + ε))
            (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
            (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
            (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
              Grescale ε F (WithLp.toLp 2 x))))
            (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
              Grescale ε F (WithLp.toLp 2 x)))) := hnative
      _ ≤ 2 * (Cb * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
              (N : ℝ) / Real.log N ^ (9 * (k : ℝ) + 3)) +
            PrimeGaps.correctedCrossNativeError m (9 * k + 3)
              Cd C₀ C₁ C₂ N (W N) (R ^ (1 + ε))
              (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
              (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
              (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x))))
              (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x)))) := hbridge
      _ ≤ (2 * Cb * K_W / (θ / 2 - δ) ^ k) * PrimeGaps.secondMomentErrorScale k N R (W N)
            (MaynardSmoothY.Fmax (Grescale ε F)) + ((Cd * Cy ^ 2 * (1 + ε) ^ 2 /
                (θ / 2 - δ) ^ (k - 2) + Cd * K_W / (θ / 2 - δ) ^ k + Cd * Cy ^ 2 * (1 + ε) ^ 2 /
                (θ / 2 - δ) ^ (k - 2) + Cd * K_W / (θ / 2 - δ) ^ k + Cd * Cy ^ 2 * (1 + ε) ^ 2 /
                (θ / 2 - δ) ^ (k - 2) + Cd * K_W / (θ / 2 - δ) ^ k +
              (C₀ + C₁ + C₂) * (1 + ε) ^ (k + 1) * (θ / 2 - δ)) *
                PrimeGaps.secondMomentErrorScale k N R (W N)
                  (MaynardSmoothY.Fmax (Grescale ε F))) :=
        add_le_add htail hnorm
      _ = K * PrimeGaps.secondMomentErrorScale k N R (W N)
          (MaynardSmoothY.Fmax (Grescale ε F)) := by dsimp [K]; ring
  have hS0 : 0 ≤ PrimeGaps.secondMomentErrorScale k N R (W N)
      (MaynardSmoothY.Fmax (Grescale ε F)) := by
    unfold PrimeGaps.secondMomentErrorScale
    have hlogR : 0 ≤ Real.log R := log_sieveTruncation_nonneg N hN1 hδ.2
    positivity
  have hlower := (abs_le.mp habs).1
  linarith

-- The fixed-width error assembly elaborates several large normalized inequalities.
/-- A fixed-width lower bound for the retained square. -/
theorem retainedSquare_fixedWidth_lower {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (m : Fin k) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 < η)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N),
        (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
      PrimeGaps.S₂m h (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))) N w₀ m ≥
        PrimeGaps.profileSecondMomentMainTerm N (R ^ (1 + ε)) (W N) m
            (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
              (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) -
          C * PrimeGaps.profileSecondMomentErrorScale N R (W N)
            (MaynardSmoothY.Fmax (Grescale ε F))
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
  obtain ⟨C, hC, Nf, hf⟩ := retained_fromYm_weak hk h hadm.1.injective m ε hε F hF
      hFsupp θ δ hθ hθ' hBV hδ hεθ
      (9 * k + 3) (by positivity)
  obtain ⟨C₀, hC₀, Ni₀, hi₀⟩ := base_ymDiagonal_to_inverse hk m ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨C₁, hC₁, Ni₁, hi₁⟩ := retained_ymDiagonal_to_inverse hk m ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨C₂, hC₂, Ni₂, hi₂⟩ := discarded_ymDiagonal_to_inverse hk m ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨C₃, hC₃, Ns, hs⟩ := retainedInverse_ge_fixedWidthDecoupled hk ε η hε hη m F hF
      hFsupp θ δ hθ hδ hεθ
  obtain ⟨C₄, hC₄, Ne, he⟩ := fixedWidth_retainedProfile_eval hk ε η hε m F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨Cy, hCy, Ny, hy⟩ := corrected_ym_sup_le_weak m hk ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨K_W, hKW, NW, hW⟩ := PrimeGaps.rsq_Wasymp (k := k)
  obtain ⟨Ng, hg⟩ := PrimeGaps.ym_phiW_logR_large δ θ hδ
  let Kold := C * Cy ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k +
      C * Cy ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k +
      C * Cy ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k +
      C * Cy ^ 2 * (1 + ε) ^ 2 / (θ / 2 - δ) ^ (k - 2) + C * K_W / (θ / 2 - δ) ^ k +
      (C₀ + C₁ + C₂) * (1 + ε) ^ (k + 1) * (θ / 2 - δ)
  let Ksm := (C₃ + C₄) * (1 + ε) ^ (k + 1) * (θ / 2 - δ)
  refine ⟨Kold + Ksm + 1, ?_, ?_⟩
  · have hc : 0 < θ / 2 - δ := by linarith [hδ.2]
    have hko : 0 ≤ Kold := by dsimp [Kold]; positivity
    have hks : 0 ≤ Ksm := by dsimp [Ksm]; positivity
    linarith
  refine ⟨(max Nf (max Ni₀ (max Ni₁ (max Ni₂ (max Ns (max Ne (max Ny
    (max NW (max Ng (rexp (rexp (rexp 2)))))))))))), ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hNf, hNi₀, hNi₁, hNi₂, hNs, hNe, hNy, hNW, hNg, hNexp⟩ := hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos _) hNexp
    exact_mod_cast this
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
  have hlogN : 1 ≤ Real.log N := by
    have hinside : (1 : ℝ) ≤ rexp (rexp 2) := Real.one_le_exp (Real.exp_pos 2).le
    have h1 : rexp 1 ≤ (N : ℝ) := le_trans (Real.exp_le_exp.2 hinside) hNexp
    have ht := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at ht
  obtain ⟨hW1, hWa⟩ := hW N hNW
  obtain ⟨hD0, _, _⟩ := hg N hNg
  have hfrom := hf N hNf w₀ hw₀
  have hinv := hi₁ N hNi₁
  have hsmooth := hs N hNs
  have heval := he N hNe
  obtain ⟨hU₀, hU₁, hU₂⟩ := hy N hNy
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k := support_rescale_subset hε hFsupp
  have hY₀ : (PrimeGaps.lToY
        (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))).maxRealAbs ≤
          MaynardSmoothY.Fmax (Grescale ε F) :=
    maxRealAbs_l₀_le_Fmax hk hNpos δ θ ε hG hGsupp
  have hY₁ : (PrimeGaps.lToY
        (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F) :=
    maxRealAbs_retainedL_le_Fmax hk hNpos δ θ ε m hG hGsupp
  have hY₂ : (PrimeGaps.lToY
        (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x))))).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F) :=
    maxRealAbs_discardedL_le_Fmax hk hNpos δ θ ε m hG hGsupp
  have hnorm := correctedCrossNativeError_le hk hN1 m δ θ ε F hF
    C C₀ C₁ C₂ Cy Cy K_W hC hCy hCy hKW
    hε hδ hlogN hD0 hW1 hWa
    hU₀ hU₁ hU₂
    hY₀ hY₁ hY₂
  have hweaknorm := weakFromYmError_le_s2ErrBase hk hN1 m δ θ ε F hF
    C Cy K_W hC hCy hKW hε hδ hlogN hD0 hW1 hWa hU₁
  let a : ℝ := (N : ℝ) / (((W N).totient : ℝ) * Real.log N)
  let L₁ := retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
    Grescale ε F (WithLp.toLp 2 x)))
  let Y := PrimeGaps.ymDiagonalForm m (W N) L₁
  let Z := PrimeGaps.inverseDiagonalForm m (W N) L₁
  let D := decoupledSum (R ^ (1 + ε)) (W N) (PrimeGaps.retainedProfile ε η m (Grescale ε F)) m
  let Q := ((W N).totient : ℝ) ^ (k + 1) * Real.log (R ^ (1 + ε)) ^ (k + 1) / (W N : ℝ) ^ (k + 1) *
      PrimeGaps.J m
          (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
            (Grescale_contDiff hF)
            (support_rescale_subset hε hFsupp))
  let Eold := PrimeGaps.correctedCrossNativeError m (9 * k + 3)
      C C₀ C₁ C₂ N (W N) (R ^ (1 + ε)) (MaynardSmoothY.Fmax (Grescale ε F))
      (PrimeGaps.D₀ (N : ℝ))
      (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) L₁
      (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x)))) + PrimeGaps.weakFromYmError m (9 * k + 3) C N (W N)
          (MaynardSmoothY.Fmax (Grescale ε F)) L₁
  let EP := MaynardSmoothY.Fmax
      (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ^ 2 * ((W N).totient : ℝ) ^ (k + 1) *
    Real.log (R ^ (1 + ε)) ^ (k + 1) / ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ))
  have hlr : 0 ≤ Real.log R := log_sieveTruncation_nonneg N hN1 hδ.2
  have hlraux : 0 ≤ Real.log (R ^ (1 + ε)) := by
    rw [Real.log_rpow (by positivity)]
    exact mul_nonneg (by linarith) hlr
  have ha : 0 ≤ a := by
    dsimp [a]
    positivity
  have hnative : PrimeGaps.weakFromYmError m (9 * k + 3) C N (W N)
            (MaynardSmoothY.Fmax (Grescale ε F)) L₁ +
          a * PrimeGaps.inverseDiagonalApproxErrorScale k C₁ (R ^ (1 + ε)) (W N)
            (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) ≤ Eold := by
    dsimp [Eold, PrimeGaps.correctedCrossNativeError, L₁, a]
    have hφ : 0 < ((W N).totient : ℝ) := PrimeGaps.totient_W_pos
    have hlog : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hlogN
    have hnonneg0 : 0 ≤ PrimeGaps.fromYmError m (9 * k + 3) C N (W N)
        (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) :=
      PrimeGaps.fromYmError_nonneg m _ C _ hC.le hlog hD0
    have hnonneg1 : 0 ≤ PrimeGaps.fromYmError m (9 * k + 3) C N (W N)
        (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x)))) :=
      PrimeGaps.fromYmError_nonneg m _ C _ hC.le hlog hD0
    have hnonneg2 : 0 ≤ PrimeGaps.fromYmError m (9 * k + 3) C N (W N)
        (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
          Grescale ε F (WithLp.toLp 2 x)))) :=
      PrimeGaps.fromYmError_nonneg m _ C _ hC.le hlog hD0
    have hi0 : 0 ≤ PrimeGaps.inverseDiagonalApproxErrorScale k C₀ (R ^ (1 + ε)) (W N)
        (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) :=
      PrimeGaps.inverseDiagonalApproxErrorScale_nonneg k C₀ (R ^ (1 + ε)) (W N)
        (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) hC₀ hlraux hD0.le
    have hi2 : 0 ≤ PrimeGaps.inverseDiagonalApproxErrorScale k C₂ (R ^ (1 + ε)) (W N)
        (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) :=
      PrimeGaps.inverseDiagonalApproxErrorScale_nonneg k C₂ (R ^ (1 + ε)) (W N)
        (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) hC₂ hlraux hD0.le
    have ha0 : 0 ≤ (N : ℝ) / (((W N).totient : ℝ) * Real.log N) := by positivity
    linarith only [mul_nonneg ha0 (add_nonneg hi0 hi2), hnonneg0, hnonneg1, hnonneg2]
  have hfixed0 : 0 ≤ PrimeGaps.profileSecondMomentErrorScale N R (W N)
      (MaynardSmoothY.Fmax (Grescale ε F))
      (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
    unfold PrimeGaps.profileSecondMomentErrorScale
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (pow_nonneg (by
              exact_mod_cast (Nat.zero_le (W N).totient)) _))
          (by positivity))
        (pow_nonneg hlr _))
      (mul_nonneg
        (pow_nonneg (by exact_mod_cast (Nat.zero_le (W N))) _)
        hD0.le)
  have hold : Eold ≤ Kold * PrimeGaps.profileSecondMomentErrorScale N R (W N)
      (MaynardSmoothY.Fmax (Grescale ε F))
      (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
    have hn : Eold ≤ Kold * PrimeGaps.secondMomentErrorScale k N R (W N)
        (MaynardSmoothY.Fmax (Grescale ε F)) := by
      dsimp [Eold, Kold]
      calc _
          ≤ _ := add_le_add hnorm hweaknorm
        _ = _ := by ring
    have hdom := @PrimeGaps.secondMomentErrorScale_le_profileSecondMomentErrorScale k N (W N)
      R (MaynardSmoothY.Fmax (Grescale ε F))
      (PrimeGaps.retainedProfile ε η m (Grescale ε F)) hlr hD0.le
    have hc : 0 < θ / 2 - δ := by linarith [hδ.2]
    have hKold0 : 0 ≤ Kold := by
      dsimp [Kold]
      positivity
    exact hn.trans (mul_le_mul_of_nonneg_left hdom hKold0)
  have hsm : a * ((C₃ + C₄) * EP) ≤ Ksm * PrimeGaps.profileSecondMomentErrorScale N R (W N)
        (MaynardSmoothY.Fmax (Grescale ε F))
        (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
    have ht := fixedWidth_inverse_error_absorb (C₃ + C₄) δ θ ε η m F
        hN1 (add_nonneg hC₃ hC₄) hε hδ
        (lt_of_lt_of_le zero_lt_one hlogN) hD0
    convert ht using 1
    all_goals simp only [a, EP]
    all_goals ring
  have hfrom' :
      |PrimeGaps.S₂m h (⇑L₁) N w₀ m - a * Y| ≤ PrimeGaps.weakFromYmError m (9 * k + 3) C N (W N)
          (MaynardSmoothY.Fmax (Grescale ε F)) L₁ := by
    simpa [a, Y, L₁] using hfrom
  have hinv' : |Y - Z| ≤ PrimeGaps.inverseDiagonalApproxErrorScale k C₁
      (R ^ (1 + ε)) (W N) (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) := by
    simpa [Y, Z, L₁, PrimeGaps.inverseDiagonalApproxErrorScale] using hinv
  have hsmooth' : Z ≥ D - C₃ * EP := by
    convert hsmooth using 1
    all_goals simp only [D, EP]
    all_goals ring
  have heval' : |D - Q| ≤ C₄ * EP := by
    convert heval using 1
    all_goals simp only [EP]
    all_goals ring
  have hchain : PrimeGaps.S₂m h (⇑L₁) N w₀ m ≥ a * Q - Eold - a * ((C₃ + C₄) * EP) := by
    have hflo := (abs_le.mp hfrom').1
    have hilo := (abs_le.mp hinv').1
    have helo := (abs_le.mp heval').1
    have hEP0 : 0 ≤ EP := by
      dsimp [EP]
      exact div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _)
            (pow_nonneg (by exact_mod_cast (Nat.zero_le (W N).totient)) _))
          (pow_nonneg hlraux _))
        (mul_nonneg
          (pow_nonneg (by exact_mod_cast (Nat.zero_le (W N))) _)
          hD0.le)
    have hstep1 : a * Y ≥ a * Z - a * PrimeGaps.inverseDiagonalApproxErrorScale k C₁
        (R ^ (1 + ε)) (W N) (MaynardSmoothY.Fmax (Grescale ε F))
          (PrimeGaps.D₀ (N : ℝ)) := by
      linarith [mul_le_mul_of_nonneg_left hilo ha]
    have hstep2 : a * Z ≥ a * D - a * (C₃ * EP) := by
      linarith [mul_le_mul_of_nonneg_left hsmooth' ha]
    have hstep3 : a * D ≥ a * Q - a * (C₄ * EP) := by linarith [mul_le_mul_of_nonneg_left helo ha]
    have hn := hnative
    have herr : a * (C₃ * EP) + a * (C₄ * EP) = a * ((C₃ + C₄) * EP) := by ring
    linarith
  have hmain : a * Q = PrimeGaps.profileSecondMomentMainTerm N (R ^ (1 + ε)) (W N) m
      (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
        (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) := by
    dsimp [a, Q, PrimeGaps.profileSecondMomentMainTerm]
    have hφ : ((W N).totient : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Nat.totient_pos.mpr PrimeGaps.W_pos))
    have hlog : Real.log (N : ℝ) ≠ 0 := (lt_of_lt_of_le zero_lt_one hlogN).ne'
    field_simp
    ring
  rw [← hmain]
  have htotal : Eold + a * ((C₃ + C₄) * EP) ≤ (Kold + Ksm + 1) *
        PrimeGaps.profileSecondMomentErrorScale N R (W N) (MaynardSmoothY.Fmax (Grescale ε F))
          (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
    have hexp : (Kold + Ksm + 1) * PrimeGaps.profileSecondMomentErrorScale N R (W N)
          (MaynardSmoothY.Fmax (Grescale ε F))
          (PrimeGaps.retainedProfile ε η m (Grescale ε F)) =
        Kold * PrimeGaps.profileSecondMomentErrorScale N R (W N)
            (MaynardSmoothY.Fmax (Grescale ε F))
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) +
          Ksm * PrimeGaps.profileSecondMomentErrorScale N R (W N)
            (MaynardSmoothY.Fmax (Grescale ε F))
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) +
          PrimeGaps.profileSecondMomentErrorScale N R (W N) (MaynardSmoothY.Fmax (Grescale ε F))
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by ring
    linarith
  linarith

/-- A second-moment lower bound with fixed smoothing width as `N → ∞`. -/
theorem prop_s2_fixedWidth {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (m : Fin k) (ε η : ℝ) (hε : 0 ≤ ε) (hη : 0 < η)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N),
        (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
      PrimeGaps.S₂m h (lambdaEps k N δ θ ε F) N w₀ m ≥
        PrimeGaps.profileSecondMomentMainTerm N (R ^ (1 + ε)) (W N) m
            (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
              (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) -
          C * PrimeGaps.profileSecondMomentErrorScale N R (W N)
            (MaynardSmoothY.Fmax (Grescale ε F))
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
  obtain ⟨C₁, hC₁, N₁, hret⟩ := retainedSquare_fixedWidth_lower hk h hadm m ε η hε hη F hF
      hFsupp θ δ hθ hθ' hBV hδ hεθ
  obtain ⟨C₂, hC₂, N₂, hcross⟩ := crossTerm_negligible hk h hadm m ε hε F hF hFsupp θ δ hθ
      hθ' hBV hδ hεθ
  obtain ⟨Ng, hg⟩ := PrimeGaps.ym_phiW_logR_large δ θ hδ
  refine ⟨C₁ + C₂ + 1, by linarith, max N₁ (max N₂ Ng), ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hN₁, hN₂, hNg⟩ := hN
  have hretN := hret N hN₁ w₀ hw₀
  have hcrossN := hcross N hN₂ w₀ hw₀
  obtain ⟨hD0, _, _⟩ := hg N hNg
  have hNpos : 0 < N := by
    by_contra hz
    have hNz : N = 0 := Nat.eq_zero_of_not_pos hz
    subst N
    norm_num [PrimeGaps.D₀] at hD0
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr hNpos.ne'
  have hlogN : 0 ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast hN1)
  have hlr : 0 ≤ Real.log R := log_sieveTruncation_nonneg N hN1 hδ.2
  have hdom := @PrimeGaps.secondMomentErrorScale_le_profileSecondMomentErrorScale k N (W N)
    R (MaynardSmoothY.Fmax (Grescale ε F))
    (PrimeGaps.retainedProfile ε η m (Grescale ε F)) hlr hD0.le
  have hsplit := corrected_retained_split_lower hN1 h δ θ ε hε m F w₀
  have hfixed0 : 0 ≤ PrimeGaps.profileSecondMomentErrorScale N R (W N)
      (MaynardSmoothY.Fmax (Grescale ε F))
      (PrimeGaps.retainedProfile ε η m (Grescale ε F)) := by
    unfold PrimeGaps.profileSecondMomentErrorScale
    exact div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))
            (pow_nonneg (by exact_mod_cast (Nat.zero_le (W N).totient)) _))
          (by positivity))
        (pow_nonneg hlr _))
      (mul_nonneg
        (pow_nonneg (by exact_mod_cast (Nat.zero_le (W N))) _)
        hD0.le)
  have hcdom := mul_le_mul_of_nonneg_left hdom hC₂.le
  linarith


end Gaps246
