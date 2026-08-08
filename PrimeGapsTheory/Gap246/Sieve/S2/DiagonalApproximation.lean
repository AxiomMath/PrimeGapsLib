/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.WeightBounds


/-!
# Diagonal approximation

Weak-room comparisons between transformed weighted sums and inverse diagonal forms.
-/

@[expose] public section

open scoped ArithmeticFunction.detotient

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY PrimeGaps
open scoped PrimeGaps PrimeGaps.sieveTruncation PrimeGaps.sieveModulus

namespace Gaps246

/-- Retained substitution bounded in the smooth norm. -/
theorem retained_S2m_substitute_ym_weak_Fmax {k : ℕ} (hk : 2 ≤ k)
    (h : Fin k → ℕ) (hinj : Function.Injective h) (m : Fin k)
    (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N),
        (∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (W N) = 1) →
      |PrimeGaps.S₂m h (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))) N w₀ m - (Nat.primeCountingIoc N (2 * N) : ℝ) /
            (W N).totient * PrimeGaps.ymWeightedSum m
              (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x))))| ≤ C * MaynardSmoothY.Fmax (Grescale ε F) ^
                2 *
            (N : ℝ) / Real.log N ^ A := by
  obtain ⟨Ccrt, hCcrt, Ncrt, hcrt⟩ := retained_S2m_crt_weak h hinj m ε hε F θ δ hθ hδ hεθ
  obtain ⟨Cbv, Nbv, hCbv, hbv⟩ := retained_twoWeightError_bound_Fmax hk m A hA ε hε
      F hF hFsupp θ δ hθ hθ' hBV hδ hεθ
  refine ⟨Ccrt * Cbv, by positivity, max Ncrt Nbv, ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hNcrt, hNbv⟩ := hN
  have hc := hcrt N hNcrt w₀ hw₀
  have hb := hbv N hNbv
  calc
    |PrimeGaps.S₂m h (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))) N w₀ m - (Nat.primeCountingIoc N (2 * N) : ℝ) /
            (W N).totient * PrimeGaps.ymWeightedSum m
              (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x))))| ≤
        Ccrt * PrimeGaps.twoWeightError k (N : ℝ) (W N) m
          (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))) := hc
    _ ≤ Ccrt * (Cbv * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ A) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Ccrt * Cbv *
        MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ A := by ring

theorem corrected_ym_sup_le_weak {k : ℕ} (m : Fin k) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → (⨆ r, |PrimeGaps.ym m
          (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) r|) ≤ C *
            MaynardSmoothY.Fmax (Grescale ε F) *
            ((W N).totient : ℝ) * Real.log (R ^ (1 + ε)) / (W N : ℝ) ∧
      (⨆ r, |PrimeGaps.ym m (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x)))) r|) ≤ C * MaynardSmoothY.Fmax (Grescale ε F) *
            ((W N).totient : ℝ) * Real.log (R ^ (1 + ε)) / (W N : ℝ) ∧
      (⨆ r, |PrimeGaps.ym m (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x)))) r|) ≤ C * MaynardSmoothY.Fmax (Grescale ε F) *
            ((W N).totient : ℝ) * Real.log (R ^ (1 + ε)) / (W N : ℝ) := by
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k := support_rescale_subset hε hFsupp
  obtain ⟨C, hC, N₀, hb⟩ := PrimeGaps.S2mSmooth.ym_sup_le_of_maxRealAbs m (Grescale ε F) hG hGsupp
      (auxTheta δ θ ε) (auxDelta δ θ ε) hΘ hΔ
  simp_rw [aux_sieveTruncation_eq] at hb
  refine ⟨C, hC, max N₀ 1, ?_⟩
  intro N hN
  have hNN₀ : N₀ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by
    have : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
    exact_mod_cast lt_of_lt_of_le zero_lt_one this
  have h0 := hb N hNN₀ (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
    PrimeGaps.hasPermissibleSupport_l₀
    (maxRealAbs_l₀_le_Fmax hk hNpos δ θ ε hG hGsupp)
  have h1 := hb N hNN₀ (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 +
    ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
    (retainedL_hasPermissibleSupport (R ^ (1 - ε)) m _
      PrimeGaps.hasPermissibleSupport_l₀)
    (maxRealAbs_retainedL_le_Fmax hk hNpos δ θ ε m hG hGsupp)
  have h2 := hb N hNN₀ (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 +
    ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
    (discardedL_hasPermissibleSupport (R ^ (1 - ε)) m _
      PrimeGaps.hasPermissibleSupport_l₀)
    (maxRealAbs_discardedL_le_Fmax hk hNpos δ θ ε m hG hGsupp)
  exact ⟨h0, h1, h2⟩

theorem retained_fromYm_weak {k : ℕ} (hk : 2 ≤ k)
    (h : Fin k → ℕ) (hinj : Function.Injective h) (m : Fin k)
    (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ)
    (A : ℝ) (hA : 0 < A) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N),
        (∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (W N) = 1) →
      |PrimeGaps.S₂m h (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
            Grescale ε F (WithLp.toLp 2 x))))) N w₀ m - ((N : ℝ) /
            (((W N).totient : ℝ) * Real.log N)) * PrimeGaps.ymDiagonalForm m (W N)
              (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x))))| ≤
            PrimeGaps.weakFromYmError m A C N (W N) (MaynardSmoothY.Fmax (Grescale ε F))
              (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x)))) := by
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  obtain ⟨Cs, hCs, Ns, hs⟩ := retained_S2m_substitute_ym_weak_Fmax hk h hinj m ε hε
      F hF hFsupp θ δ hθ hθ' hBV hδ hεθ A hA
  obtain ⟨Cd, hCd, Nd, hd⟩ := ymWeightedSum_to_diagonal m hk (auxTheta δ θ ε) (auxDelta δ θ ε) hΘ hΔ
  obtain ⟨Cp, hCp, Np, hp⟩ := lem_S2m_PNT m (auxTheta δ θ ε) (auxDelta δ θ ε)
      hk hΘ hΔ
  simp_rw [aux_sieveTruncation_eq] at hd hp
  let C := Cs + Cd + Cp + 1
  have hC : 0 < C := by
    dsimp [C]
    linarith only [hCs, hCd, hCp]
  refine ⟨C, hC, max Ns (max Nd Np), ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hNs, hNd, hNp⟩ := hN
  let L := retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
    Grescale ε F (WithLp.toLp 2 x)))
  let pref : ℝ := (Nat.primeCountingIoc N (2 * N) : ℝ) / (W N).totient
  let mainPref : ℝ := (N : ℝ) / (((W N).totient : ℝ) * Real.log N)
  let Sig : ℝ := ∑' u : Fin k → ℕ, if (∀ i, 1 ≤ u i) ∧ PrimeGaps.LemS1RestrictSij.RestrictedCoprime
            u (fun _ _ ↦ 1)
      then PrimeGaps.ym m L u ^ 2 / ∏ i, (g (u i) : ℝ)
      else 0
  have hL : L.HasPermissibleSupport ⌊R ^ (1 + ε)⌋₊ (W N) :=
    retainedL_hasPermissibleSupport (R ^ (1 - ε)) m _
      PrimeGaps.hasPermissibleSupport_l₀
  have hsub := hs N hNs w₀ hw₀
  have hdrop := hd N hNd L hL
  have hpnt := hp N hNp L hL
  have hdiag : Sig = PrimeGaps.ymDiagonalForm m (W N) L := by
    dsimp [Sig]
    exact PrimeGaps.fromYm_diagonal_eq_ymDiagonalForm m (R ^ (1 + ε)) (W N) L hL
  have htri :
      |PrimeGaps.S₂m h (⇑L) N w₀ m -
          mainPref * PrimeGaps.ymDiagonalForm m (W N) L| ≤ |PrimeGaps.S₂m h (⇑L) N w₀ m -
              pref * PrimeGaps.ymWeightedSum m L| +
            |pref * PrimeGaps.ymWeightedSum m L - pref * Sig| +
          |pref * Sig - mainPref * Sig| := by
    rw [← hdiag]
    have h₁ := abs_sub_le (PrimeGaps.S₂m h (⇑L) N w₀ m) (pref * PrimeGaps.ymWeightedSum m L)
      (mainPref * Sig)
    have h₂ := abs_sub_le (pref * PrimeGaps.ymWeightedSum m L) (pref * Sig) (mainPref * Sig)
    linarith only [h₁, h₂]
  have hsub' :
      |PrimeGaps.S₂m h (⇑L) N w₀ m -
          pref * PrimeGaps.ymWeightedSum m L| ≤ Cs * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
            (N : ℝ) / Real.log N ^ A := by
    simpa only [L, pref] using hsub
  have hdrop' :
      |pref * PrimeGaps.ymWeightedSum m L - pref * Sig| ≤ Cd * (⨆ r, |PrimeGaps.ym m L r|) ^ 2 *
            ((W N).totient : ℝ) ^ (k - 2) * (N : ℝ) * Real.log N ^ (k - 2) /
            ((W N : ℝ) ^ (k - 1) *
                PrimeGaps.D₀ (N : ℝ)) := by
    simpa only [L, pref, Sig] using hdrop
  have hpnt' :
      |pref * Sig - mainPref * Sig| ≤ Cp * (⨆ r, |PrimeGaps.ym m L r|) ^ 2 *
            ((W N).totient : ℝ) ^ (k - 2) * (N : ℝ) * Real.log N ^ (k - 2) /
            ((W N : ℝ) ^ (k - 1) *
                PrimeGaps.D₀ (N : ℝ)) := by
    simpa only [L, pref, mainPref, Sig] using hpnt
  let Ediag : ℝ := (⨆ r, |PrimeGaps.ym m L r|) ^ 2 *
      ((W N).totient : ℝ) ^ (k - 2) * (N : ℝ) * Real.log N ^ (k - 2) /
      ((W N : ℝ) ^ (k - 1) * PrimeGaps.D₀ (N : ℝ))
  let Esub : ℝ := MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ A
  have hsubN : |PrimeGaps.S₂m h (⇑L) N w₀ m - pref * PrimeGaps.ymWeightedSum m L| ≤ Cs * Esub :=
    calc _
        ≤ _ := hsub'
      _ = Cs * Esub := by dsimp [Esub]; ring
  have hdropN : |pref * PrimeGaps.ymWeightedSum m L - pref * Sig| ≤ Cd * Ediag :=
    calc _
        ≤ _ := hdrop'
      _ = Cd * Ediag := by dsimp [Ediag]; ring
  have hpntN : |pref * Sig - mainPref * Sig| ≤ Cp * Ediag :=
    calc _
        ≤ _ := hpnt'
      _ = Cp * Ediag := by dsimp [Ediag]; ring
  have hEd : 0 ≤ Ediag := by
    have habs : 0 ≤ |pref * Sig - mainPref * Sig| := abs_nonneg _
    by_contra hE
    exact (not_lt_of_ge (habs.trans hpntN)) (mul_neg_of_pos_of_neg hCp (lt_of_not_ge hE))
  have hEs : 0 ≤ Esub := by
    have habs : 0 ≤ |PrimeGaps.S₂m h (⇑L) N w₀ m - pref * PrimeGaps.ymWeightedSum m L| :=
      abs_nonneg _
    by_contra hE
    exact (not_lt_of_ge (habs.trans hsubN)) (mul_neg_of_pos_of_neg hCs (lt_of_not_ge hE))
  have hsum :
      |PrimeGaps.S₂m h (⇑L) N w₀ m - pref * PrimeGaps.ymWeightedSum m L| +
          |pref * PrimeGaps.ymWeightedSum m L - pref * Sig| +
          |pref * Sig - mainPref * Sig| ≤ Cs * Esub + (Cd + Cp) * Ediag :=
    calc _
        ≤ Cs * Esub + Cd * Ediag + Cp * Ediag := add_le_add (add_le_add hsubN hdropN) hpntN
      _ = Cs * Esub + (Cd + Cp) * Ediag := by ring
  have hCsC : Cs ≤ C := by
    dsimp [C]
    linarith only [hCd, hCp]
  have hCdCpC : Cd + Cp ≤ C := by
    dsimp [C]
    linarith only [hCs]
  have hnorm : Cs * Esub + (Cd + Cp) * Ediag ≤ C * Ediag + C * Esub :=
    calc _
        ≤ C * Esub + C * Ediag := add_le_add (mul_le_mul_of_nonneg_right hCsC hEs)
            (mul_le_mul_of_nonneg_right hCdCpC hEd)
      _ = C * Ediag + C * Esub := by ring
  calc _
      ≤ _ := htri
    _ ≤ _ := hsum
    _ ≤ C * Ediag + C * Esub := hnorm
    _ = PrimeGaps.weakFromYmError m A C N (W N) (MaynardSmoothY.Fmax (Grescale ε F)) L := by
      dsimp [PrimeGaps.weakFromYmError, PrimeGaps.fromYmErrorScale,
        PrimeGaps.weightedDiagonalErrorScale, Ediag, Esub, L]
      ring

/-- The `ym` form of a permissibly supported weight is approximated by its inverse form at the
auxiliary truncation. -/
theorem ym_to_yInverse_of_permissible {k : ℕ} (hk : 2 ≤ k)
    (m : Fin k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ)
    (L : ℕ → ((Fin k → ℕ) →₀ ℝ))
    (hLsupp : ∀ N : ℕ, (L N).HasPermissibleSupport ⌊R ^ (1 + ε)⌋₊ (W N))
    (hLmax : ∀ N : ℕ, 0 < N →
      (PrimeGaps.lToY (L N)).maxRealAbs ≤ MaynardSmoothY.Fmax (Grescale ε F)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      |(∑' r : Fin k → ℕ, if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N))
          then (PrimeGaps.ym m (L N) r) ^ 2 / (∏ i ∈ Finset.univ.erase m,
                    (g (r i) : ℝ))
          else 0) - (∑' r : Fin k → ℕ,
          if r m = 1 ∧ (∀ i, i ≠ m → 1 ≤ r i ∧ (r i).Coprime (W N))
          then (yInverseSum (L N) m r) ^ 2 / (∏ i ∈ Finset.univ.erase m,
                    (g (r i) : ℝ))
          else 0)| ≤ C * (MaynardSmoothY.Fmax (Grescale ε F)) ^ 2 * ((W N).totient : ℝ) ^ (k + 1) *
            Real.log (R ^ (1 + ε)) ^ (k + 1) /
            ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  have hG : ContDiff ℝ (⊤ : ℕ∞) (Grescale ε F) := Grescale_contDiff hF
  have hGsupp : Function.support (Grescale ε F) ⊆ 𝓡 k := support_rescale_subset hε hFsupp
  obtain ⟨C, hC, hbody⟩ := PrimeGaps.lem_S2m_second_moment hk
  obtain ⟨H, hHadm, hHcard⟩ := PrimeGaps.S2mSmooth.exists_admissible_card k
  obtain ⟨N₀, hN₀⟩ := hbody
    H hHadm hHcard (auxTheta δ θ ε) (auxDelta δ θ ε) hΘ hΔ.1 hΔ.2
    (Grescale ε F) hG hGsupp
  simp_rw [aux_sieveTruncation_eq] at hN₀
  refine ⟨C, hC, max N₀ 1, ?_⟩
  intro N hN
  have hNpos : 0 < N := by
    have hN1 : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
    exact_mod_cast lt_of_lt_of_le zero_lt_one hN1
  exact hN₀ N ((le_max_left _ _).trans hN) (L N) (hLsupp N) (hLmax N hNpos) m

/-- The total `ymDiagonalForm` is approximated by its inverse diagonal form. -/
theorem base_ymDiagonal_to_inverse {k : ℕ} (hk : 2 ≤ k) (m : Fin k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      |PrimeGaps.ymDiagonalForm m (W N) (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x))) - PrimeGaps.inverseDiagonalForm m (W N)
              (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))| ≤
                PrimeGaps.inverseDiagonalApproxErrorScale k C (R ^ (1 + ε)) (W N)
                  (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) := by
  simpa [PrimeGaps.ymDiagonalForm, PrimeGaps.ymDiagonalTerm, PrimeGaps.inverseDiagonalForm,
    PrimeGaps.inverseDiagonalTerm, PrimeGaps.inverseDiagonalApproxErrorScale,
    aux_sieveTruncation_eq] using
    ym_to_yInverse_of_permissible hk m ε hε F hF hFsupp θ δ hθ hδ hεθ
      (fun N ↦ PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
      (fun _ ↦ PrimeGaps.hasPermissibleSupport_l₀)
      (fun N hNpos ↦ maxRealAbs_l₀_le_Fmax hk hNpos δ θ ε (Grescale_contDiff hF)
        (support_rescale_subset hε hFsupp))

/-- The retained `ymDiagonalForm` is approximated by its inverse diagonal form. -/
theorem retained_ymDiagonal_to_inverse {k : ℕ} (hk : 2 ≤ k) (m : Fin k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      |PrimeGaps.ymDiagonalForm m (W N) (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 +
        ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) - PrimeGaps.inverseDiagonalForm m (W N)
              (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x))))| ≤
                  PrimeGaps.inverseDiagonalApproxErrorScale k C (R ^ (1 + ε)) (W N)
                    (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) := by
  simpa [PrimeGaps.ymDiagonalForm, PrimeGaps.ymDiagonalTerm, PrimeGaps.inverseDiagonalForm,
    PrimeGaps.inverseDiagonalTerm, PrimeGaps.inverseDiagonalApproxErrorScale,
    aux_sieveTruncation_eq] using
    ym_to_yInverse_of_permissible hk m ε hε F hF hFsupp θ δ hθ hδ hεθ
      (fun N ↦ retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x))))
      (fun N ↦ retainedL_hasPermissibleSupport (R ^ (1 - ε)) m _
        PrimeGaps.hasPermissibleSupport_l₀)
      (fun N hNpos ↦ maxRealAbs_retainedL_le_Fmax hk hNpos δ θ ε m
        (Grescale_contDiff hF) (support_rescale_subset hε hFsupp))

/-- The discarded `ymDiagonalForm` is approximated by its inverse diagonal form. -/
theorem discarded_ymDiagonal_to_inverse {k : ℕ} (hk : 2 ≤ k) (m : Fin k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      |PrimeGaps.ymDiagonalForm m (W N) (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 +
        ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) - PrimeGaps.inverseDiagonalForm m (W N)
              (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                Grescale ε F (WithLp.toLp 2 x))))| ≤
                  PrimeGaps.inverseDiagonalApproxErrorScale k C (R ^ (1 + ε)) (W N)
                    (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ)) := by
  simpa [PrimeGaps.ymDiagonalForm, PrimeGaps.ymDiagonalTerm, PrimeGaps.inverseDiagonalForm,
    PrimeGaps.inverseDiagonalTerm, PrimeGaps.inverseDiagonalApproxErrorScale,
    aux_sieveTruncation_eq] using
    ym_to_yInverse_of_permissible hk m ε hε F hF hFsupp θ δ hθ hδ hεθ
      (fun N ↦ discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
        Grescale ε F (WithLp.toLp 2 x))))
      (fun N ↦ discardedL_hasPermissibleSupport (R ^ (1 - ε)) m _
        PrimeGaps.hasPermissibleSupport_l₀)
      (fun N hNpos ↦ maxRealAbs_discardedL_le_Fmax hk hNpos δ θ ε m
        (Grescale_contDiff hF) (support_rescale_subset hε hFsupp))

theorem corrected_cross_native_weak {k : ℕ} (hk : 2 ≤ k)
    (h : Fin k → ℕ) (hadm : IsAdmissible h) (m : Fin k)
    (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ Cb Cd C₀ C₁ C₂ : ℝ, 0 < Cb ∧ 0 < Cd ∧ 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ 0 ≤ C₂ ∧
      ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd
            (W N) = 1) →
        |2 * PrimeGaps.bilinearPrimeSum h N m
            (⇑(retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
              Grescale ε F (WithLp.toLp 2 x)))))
            (⇑(discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
              Grescale ε F (WithLp.toLp 2 x))))) w₀| ≤ PrimeGaps.weakCrossNativeError m (9 * k + 3)
              Cb Cd C₀ C₁ C₂ N (W N) (R ^ (1 + ε))
                (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
                (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
                (retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                  Grescale ε F (WithLp.toLp 2 x))))
                (discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
                  Grescale ε F (WithLp.toLp 2 x)))) := by
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  obtain ⟨Cb, hCb, Nb, hb⟩ := corrected_bilinearPrimeSum_substitute_weak_Fmax hk h
      hadm.1.injective m (9 * k + 3) (by positivity)
      ε hε F hF hFsupp θ δ hθ hθ' hBV hδ hεθ
  obtain ⟨Cd, hCd, Nd, hd⟩ := PrimeGaps.ymWeightedSum_to_ymDiagonal_early m hk
      (auxTheta δ θ ε) (auxDelta δ θ ε) hΘ hΔ
  simp_rw [aux_sieveTruncation_eq] at hd
  obtain ⟨C₀, hC₀, Ni₀, hi₀⟩ := base_ymDiagonal_to_inverse hk m ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨C₁, hC₁, Ni₁, hi₁⟩ := retained_ymDiagonal_to_inverse hk m ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨C₂, hC₂, Ni₂, hi₂⟩ := discarded_ymDiagonal_to_inverse hk m ε hε F hF hFsupp
      θ δ hθ hδ hεθ
  obtain ⟨Np, hp⟩ := corrected_restrictedCrossSum_polarization h hadm.1.injective m
      ε F θ δ
  refine ⟨Cb, Cd, C₀, C₁, C₂, hCb, hCd, hC₀, hC₁, hC₂,
    max Nb (max Nd (max Ni₀ (max Ni₁ (max Ni₂ (max Np 1))))), ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hNb, hNd, hNi₀, hNi₁, hNi₂, hNp, hNone⟩ := hN
  let L₀ := PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))
  let L₁ := retainedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
    Grescale ε F (WithLp.toLp 2 x)))
  let L₂ := discardedL (R ^ (1 - ε)) m (PrimeGaps.l₀ (R ^ (1 + ε)) (W N) (fun x ↦
    Grescale ε F (WithLp.toLp 2 x)))
  let B := PrimeGaps.bilinearPrimeSum h N m (⇑L₁) (⇑L₂) w₀
  let X := PrimeGaps.restrictedCrossSum h m (W N) (⇑L₁) (⇑L₂)
  let p : ℝ := (Nat.primeCountingIoc N (2 * N) : ℝ) / (W N).totient
  let a : ℝ := (N : ℝ) / (((W N).totient : ℝ) * Real.log N)
  let Y₀ := PrimeGaps.ymWeightedSum m L₀
  let Y₁ := PrimeGaps.ymWeightedSum m L₁
  let Y₂ := PrimeGaps.ymWeightedSum m L₂
  let D₀ := PrimeGaps.ymDiagonalForm m (W N) L₀
  let D₁ := PrimeGaps.ymDiagonalForm m (W N) L₁
  let D₂ := PrimeGaps.ymDiagonalForm m (W N) L₂
  let I₀ := PrimeGaps.inverseDiagonalForm m (W N) L₀
  let I₁ := PrimeGaps.inverseDiagonalForm m (W N) L₁
  let I₂ := PrimeGaps.inverseDiagonalForm m (W N) L₂
  let eb := Cb * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ (9 * k + 3 : ℝ)
  let e₀ := PrimeGaps.weightedDiagonalErrorEarly m Cd N (W N) L₀
  let e₁ := PrimeGaps.weightedDiagonalErrorEarly m Cd N (W N) L₁
  let e₂ := PrimeGaps.weightedDiagonalErrorEarly m Cd N (W N) L₂
  let q₀ := PrimeGaps.inverseDiagonalApproxErrorScale k C₀ (R ^ (1 + ε)) (W N)
    (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
  let q₁ := PrimeGaps.inverseDiagonalApproxErrorScale k C₁ (R ^ (1 + ε)) (W N)
    (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
  let q₂ := PrimeGaps.inverseDiagonalApproxErrorScale k C₂ (R ^ (1 + ε)) (W N)
    (MaynardSmoothY.Fmax (Grescale ε F)) (PrimeGaps.D₀ (N : ℝ))
  have hN1 : 1 ≤ N := by exact_mod_cast hNone
  have ha : 0 ≤ a := by dsimp [a]; positivity
  have hB : |B - p * X| ≤ eb := by simpa [B, X, p, eb] using hb N hNb w₀ hw₀
  have hpol : 2 * X = Y₀ - Y₁ - Y₂ := by
    simpa [X, Y₀, Y₁, Y₂, L₀, L₁, L₂, lambdaEpsAux_coe F hN1 hε] using hp N hNp
  have hL₀ : L₀.HasPermissibleSupport ⌊R ^ (1 + ε)⌋₊ (W N) := by
    simpa [L₀] using PrimeGaps.hasPermissibleSupport_l₀
  have hL₁ : L₁.HasPermissibleSupport ⌊R ^ (1 + ε)⌋₊ (W N) := by
    simpa [L₁] using retainedL_hasPermissibleSupport (R ^ (1 - ε)) m _
      PrimeGaps.hasPermissibleSupport_l₀
  have hL₂ : L₂.HasPermissibleSupport ⌊R ^ (1 + ε)⌋₊ (W N) := by
    simpa [L₂] using discardedL_hasPermissibleSupport (R ^ (1 - ε)) m _
      PrimeGaps.hasPermissibleSupport_l₀
  have hd₀ : |p * Y₀ - a * D₀| ≤ e₀ := by simpa [p, a, Y₀, D₀, e₀] using hd N hNd L₀ hL₀
  have hd₁ : |p * Y₁ - a * D₁| ≤ e₁ := by simpa [p, a, Y₁, D₁, e₁] using hd N hNd L₁ hL₁
  have hd₂ : |p * Y₂ - a * D₂| ≤ e₂ := by simpa [p, a, Y₂, D₂, e₂] using hd N hNd L₂ hL₂
  have hq₀ : |D₀ - I₀| ≤ q₀ := by simpa [D₀, I₀, q₀, L₀] using hi₀ N hNi₀
  have hq₁ : |D₁ - I₁| ≤ q₁ := by simpa [D₁, I₁, q₁, L₁] using hi₁ N hNi₁
  have hq₂ : |D₂ - I₂| ≤ q₂ := by simpa [D₂, I₂, q₂, L₂] using hi₂ N hNi₂
  have hinv : I₀ = I₁ + I₂ := by
    simpa [I₀, I₁, I₂, L₀, L₁, L₂] using PrimeGaps.inverseDiagonalForm_retainedL_add_discardedL
        (R ^ (1 + ε)) (R ^ (1 - ε)) m (W N) L₀
        (by simpa [L₀] using PrimeGaps.hasPermissibleSupport_l₀)
  have hout := PrimeGaps.abs_two_cross_le_of_weighted_diagonal_approximations
      B X p a Y₀ Y₁ Y₂ D₀ D₁ D₂ I₀ I₁ I₂
      eb e₀ e₁ e₂ q₀ q₁ q₂ ha hB hpol hd₀ hd₁ hd₂
      hq₀ hq₁ hq₂ hinv
  simpa [PrimeGaps.weakCrossNativeError, B, L₀, L₁, L₂, eb, e₀, e₁, e₂, q₀, q₁, q₂, a] using hout

end Gaps246
