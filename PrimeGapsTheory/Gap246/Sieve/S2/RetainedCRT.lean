/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.ProfileDefinitions


/-!
# Retained-weight CRT estimates

CRT and Bombieri--Vinogradov estimates for the retained and discarded weights.
-/

@[expose] public section

open PrimeGaps
open Finset MeasureTheory GPYSieveS1 MaynardSmoothY
open scoped PrimeGaps

namespace Gaps246
theorem epsPermissible_bilinearPrimeSum_crt_weak {k : ℕ}
    (h : Fin k → ℕ) (hinj : Function.Injective h) (m : Fin k)
    (ε : ℝ) (hε : 0 ≤ ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ Ccrt : ℝ, 0 < Ccrt ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (PrimeGaps.sieveModulus N),
        (∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1) →
      ∀ (L₁ L₂ : (Fin k → ℕ) →₀ ℝ), epsPermissible k N δ θ ε ⇑L₁ → epsPermissible k N δ θ ε ⇑L₂ →
      |PrimeGaps.bilinearPrimeSum h N m (⇑L₁) (⇑L₂) w₀ -
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.sieveModulus N).totient *
            PrimeGaps.restrictedCrossSum h m (PrimeGaps.sieveModulus N) (⇑L₁) (⇑L₂)| ≤
        Ccrt * PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N)
          m (⇑L₁) (⇑L₂) := by
  let Θ := auxTheta δ θ ε
  let Δ := auxDelta δ θ ε
  have hexp : Θ / 2 - Δ = (θ / 2 - δ) * (1 + ε) := by
    simp only [Θ, Δ, aux_exponent]
    ring
  have hexphalf : Θ / 2 - Δ < 1 / 2 := by
    have hweak : (1 + ε) * θ < 1 := (lt_div_iff₀ hθ.1).mp hεθ
    have hlt : θ / 2 - δ < θ / 2 := by linarith [hδ.1]
    have h1ε : 0 < 1 + ε := by linarith
    rw [hexp]
    nlinarith [mul_lt_mul_of_pos_left hlt h1ε]
  obtain ⟨Ccrt, hCcrt, hCRT⟩ := PrimeGaps.lem_S2m_CRT (fun i ↦ (h i : ℤ)) m
  obtain ⟨Ngap, _, hNgap⟩ := PrimeGaps.shiftGap_threshold h
  obtain ⟨Nlcm, _, hNlcm⟩ := PrimeGaps.permissibleSupport_lcm_lt h m Θ Δ hexphalf
  refine ⟨Ccrt, hCcrt, max (max Ngap Nlcm) 1, ?_⟩
  intro N hN w₀ hw₀ L₁ L₂ hp₁ hp₂
  have hNgapN : Ngap ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNlcmN : Nlcm ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  let l : (Fin k → ℕ) → ℝ := fun d ↦ |L₁ d| + |L₂ d|
  have hsupp_of_perm : ∀ (L : (Fin k → ℕ) →₀ ℝ), epsPermissible k N δ θ ε ⇑L → ∀ d, L d ≠ 0 →
      d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (Θ / 2 - Δ)⌋₊
        (PrimeGaps.sieveModulus N) := fun L hp d hd ↦
    epsPermissible_permissibleSupport_of_exponent_eq hp hexp hd
  have hsupp : ∀ d, l d ≠ 0 → d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (Θ / 2 - Δ)⌋₊
        (PrimeGaps.sieveModulus N) := by
    intro d hd
    have hor : L₁ d ≠ 0 ∨ L₂ d ≠ 0 := by
      by_contra hz
      push Not at hz
      exact hd (by simp [l, hz.1, hz.2])
    rcases hor with h1 | h2
    · exact hsupp_of_perm L₁ hp₁ d h1
    · exact hsupp_of_perm L₂ hp₂ d h2
  have hD0 : ∀ i j : Fin k, i ≠ j → (h i).dist (h j) < ⌊PrimeGaps.D₀ (N : ℝ)⌋₊ :=
    hNgap N hNgapN
  have hlcm : ∀ dd ee, l dd ≠ 0 → l ee ≠ 0 → ∀ i, (dd i).lcm (ee i) < N + h m :=
    fun dd ee hdd hee ↦ hNlcm N hNlcmN dd ee (hsupp dd hdd) (hsupp ee hee)
  have hdom₁ : ∀ d, L₁ d ≠ 0 → l d ≠ 0 := by
    intro d hd
    have : 0 < |L₁ d| + |L₂ d| := by
      have : 0 < |L₁ d| := abs_pos.mpr hd
      positivity
    simpa [l] using this.ne'
  have hdom₂ : ∀ d, L₂ d ≠ 0 → l d ≠ 0 := by
    intro d hd
    have : 0 < |L₁ d| + |L₂ d| := by
      have : 0 < |L₂ d| := abs_pos.mpr hd
      positivity
    simpa [l] using this.ne'
  exact PrimeGaps.bilinearPrimeSum_crt_bound h m hinj Θ Δ N
    (⇑L₁) (⇑L₂) w₀ hw₀ l hsupp hD0 hlcm Ccrt hCcrt hCRT
    L₁ L₂ rfl rfl hdom₁ hdom₂

/-- Weak-room CRT substitution for the retained square. -/
theorem retained_S2m_crt_weak {k : ℕ} (h : Fin k → ℕ) (hinj : Function.Injective h) (m : Fin k)
    (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ Ccrt : ℝ, 0 < Ccrt ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (PrimeGaps.sieveModulus N),
        (∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1) →
      |PrimeGaps.S₂m h (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) N w₀ m -
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.sieveModulus N).totient *
            PrimeGaps.ymWeightedSum m (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
                ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                  ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))| ≤
                    Ccrt * PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) := by
  obtain ⟨Ccrt, hCcrt, Ncrt, hcrt⟩ := epsPermissible_bilinearPrimeSum_crt_weak h hinj m ε hε
      θ δ hθ hδ hεθ
  obtain ⟨Ngap, _, hgap⟩ := PrimeGaps.exists_N0_for_D0_exceeds_h_gaps (h := h)
  obtain ⟨Ntwo, _, htwo⟩ := PrimeGaps.exists_N0_for_D0_ge_2
  refine ⟨Ccrt, hCcrt, max Ncrt (max Ngap Ntwo), ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hNcrt, hNgap, hNtwo⟩ := hN
  have hb := hcrt N hNcrt w₀ hw₀ (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
        ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
          ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
      (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
        ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
          ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
      (lambdaRetained_epsPermissible k N δ θ ε m F)
      (lambdaRetained_epsPermissible k N δ θ ε m F)
  have hself : PrimeGaps.bilinearPrimeSum h N m
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) w₀ =
                PrimeGaps.S₂m h
            (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
              ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                ε)) (PrimeGaps.sieveModulus N) (fun x ↦
                  Grescale ε F (WithLp.toLp 2 x))))) N w₀ m := by
    have hself_general (lam : (Fin k → ℕ) → ℝ) :
        PrimeGaps.bilinearPrimeSum h N m lam lam w₀ = PrimeGaps.S₂m h lam N w₀ m := by
      have hscale : PrimeGaps.S₂m h (lam + lam) N w₀ m = 4 * PrimeGaps.S₂m h lam N w₀ m := by
        unfold PrimeGaps.S₂m PrimeGaps.weight
        simp_rw [Pi.add_apply, Finset.sum_add_distrib, Finset.mul_sum]
        ring_nf
        simp only [Nat.add_comm (h m)]
      unfold PrimeGaps.bilinearPrimeSum PrimeGaps.quadraticPolarization
      dsimp only
      rw [hscale]
      ring
    exact hself_general _
  rw [hself, PrimeGaps.restrictedCrossSum_self] at hb
  let Θ := auxTheta δ θ ε
  let Δ := auxDelta δ θ ε
  have hexp : Θ / 2 - Δ = (θ / 2 - δ) * (1 + ε) := by
    simp only [Θ, Δ, aux_exponent]
    ring
  have hsuppRet : ∀ d, (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
    ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
      ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) d ≠ 0 →
      d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (Θ / 2 - Δ)⌋₊
        (PrimeGaps.sieveModulus N) := fun d hd ↦
    epsPermissible_permissibleSupport_of_exponent_eq
      (lambdaRetained_epsPermissible k N δ θ ε m F) hexp hd
  have hid : (∑' p, PrimeGaps.restrictedSummand h m (PrimeGaps.sieveModulus N)
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) p) =
                PrimeGaps.ymWeightedSum m
          (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) := by
    exact PrimeGaps.restrictedSummand_tsum_eq_ymWeightedSum h m hinj Θ Δ N
      (PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
        (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε))
          (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
      (fun d hd ↦ hsuppRet d (Finsupp.mem_support_iff.mp hd))
      (hgap N hNgap) (htwo N hNtwo)
  rwa [hid] at hb

theorem corrected_bilinearPrimeSum_crt_weak {k : ℕ}
    (h : Fin k → ℕ) (hinj : Function.Injective h) (m : Fin k)
    (ε : ℝ) (hε : 0 ≤ ε) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ Ccrt : ℝ, 0 < Ccrt ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (PrimeGaps.sieveModulus N),
        (∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1) →
      |PrimeGaps.bilinearPrimeSum h N m
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) w₀ -
        (Nat.primeCountingIoc N (2 * N) : ℝ) / (PrimeGaps.sieveModulus N).totient *
            PrimeGaps.restrictedCrossSum h m (PrimeGaps.sieveModulus N)
              (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
                ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                  ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
              (⇑(PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
                ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                  ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))| ≤
                    Ccrt * PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m
          (⇑(PrimeGaps.retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(PrimeGaps.discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) := by
  obtain ⟨Ccrt, hCcrt, Ncrt, hcrt⟩ :=
    epsPermissible_bilinearPrimeSum_crt_weak h hinj m ε hε θ δ hθ hδ hεθ
  exact ⟨Ccrt, hCcrt, Ncrt, fun N hN w₀ hw₀ ↦ hcrt N hN w₀ hw₀ _ _
    (lambdaRetained_epsPermissible k N δ θ ε m F)
    (lambdaDiscarded_epsPermissible k N δ θ ε m F)⟩

end Gaps246
