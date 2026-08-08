/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S2.InverseForms


/-!
# Bounds for transformed retained weights

Uniform smooth-norm bounds for retained and discarded transformed weights.
-/

@[expose] public section

open Real

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY PrimeGaps
open scoped PrimeGaps PrimeGaps.sieveTruncation PrimeGaps.sieveModulus

namespace Gaps246

open ArithmeticFunction zeta

/-- Pointwise divisor-weight bound for an `ε`-permissible weight whose transformed maximum is at
most `B`. -/
theorem abs_le_of_epsPermissible {k : ℕ} (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 ≤ ε) {θ δ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) (hεθ : 1 + ε < 1 / θ) {B : ℝ}
    (L : ℕ → ((Fin k → ℕ) →₀ ℝ))
    (hperm : ∀ N : ℕ, epsPermissible k N δ θ ε ⇑(L N))
    (hY : ∀ N : ℕ, 0 < N → Finsupp.maxRealAbs (PrimeGaps.lToY (L N)) ≤ B) :
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ d : Fin k → ℕ,
        |L N d| ≤ C * B * Real.log N ^ k := by
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  obtain ⟨C, N₀, hC, hb⟩ := MaynardS2Error.lambdaMax_bound k hk
      (auxTheta δ θ ε) (auxDelta δ θ ε)
      hΔ.1 hΔ.2 hΘ.2
  refine ⟨C, max N₀ 1, hC, ?_⟩
  intro N hN d
  have hNN₀ : N₀ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNpos : 0 < N := by
    have : (1 : ℝ) ≤ N := (le_max_right _ _).trans hN
    exact_mod_cast lt_of_lt_of_le zero_lt_one this
  let wL : MaynardS2Error.SieveWeights k (N : ℝ)
      (auxTheta δ θ ε) (auxDelta δ θ ε) :=
    { lam := L N
      support := by
        intro d hd
        exact epsPermissible_permissibleSupport_of_exponent_eq (hperm N)
          (by rw [aux_exponent]; ring) (Finsupp.mem_support_iff.mp hd) }
  have hlam := hb (N : ℝ) hNN₀ wL d
  dsimp [wL] at hlam
  exact hlam.trans (by
    have hp : 0 ≤ Real.log N ^ k := by positivity
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hY N hNpos) hC.le) hp)

/-- Pointwise divisor-weight bound for the retained weight in the smooth-profile norm. -/
theorem lambdaRetained_abs_le_Fmax_log {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) (m : Fin k) :
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ d : Fin k → ℕ,
        |retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
          ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
            ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) d| ≤ C *
              MaynardSmoothY.Fmax (Grescale ε F) *
              Real.log N ^ k :=
  abs_le_of_epsPermissible hk hε hθ hδ hεθ
    (fun N ↦ retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) (PrimeGaps.sieveModulus N)
        (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
    (fun N ↦ lambdaRetained_epsPermissible k N δ θ ε m F)
    (fun _ hNpos ↦ maxRealAbs_retainedL_le_Fmax hk hNpos δ θ ε m (Grescale_contDiff hF)
      (support_rescale_subset hε hFsupp))

/-- Pointwise divisor-weight bound for the discarded half of the corrected
transformed-space split. -/
theorem lambdaDiscarded_abs_le_Fmax_log {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) (m : Fin k) :
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ d : Fin k → ℕ,
        |discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
          ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
            ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) d| ≤ C *
              MaynardSmoothY.Fmax (Grescale ε F) *
              Real.log N ^ k :=
  abs_le_of_epsPermissible hk hε hθ hδ hεθ
    (fun N ↦ discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε)) m
      (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) (PrimeGaps.sieveModulus N)
        (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))
    (fun N ↦ lambdaDiscarded_epsPermissible k N δ θ ε m F)
    (fun _ hNpos ↦ maxRealAbs_discardedL_le_Fmax hk hNpos δ θ ε m (Grescale_contDiff hF)
      (support_rescale_subset hε hFsupp))

/-- A pinned pair whose outer coordinate products multiply to at most `R²` has pair modulus
below `N^θ`. -/
theorem qMod_lt_Npow_of_outer_le {k N : ℕ} {δ θ : ℝ} (m : Fin k) {d e : Fin k → ℕ}
    (hdpos : ∀ i, 0 < d i) (hepos : ∀ i, 0 < e i) (hdm : d m = 1) (hem : e m = 1)
    (hprod : (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) *
        (∏ i ∈ Finset.univ.erase m, (e i : ℝ)) ≤ PrimeGaps.sieveTruncation N δ θ ^ (2 : ℝ))
    (hWR : (PrimeGaps.sieveModulus N : ℝ) * ((N : ℝ) ^ (θ / 2 - δ)) ^ 2 < (N : ℝ) ^ θ) :
    (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e : ℝ) < (N : ℝ) ^ θ := by
  have hlcm : ((∏ i ∈ Finset.univ.erase m,
      Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤ PrimeGaps.sieveTruncation N δ θ ^ (2 : ℝ) := by
    refine le_trans ?_ hprod
    exact_mod_cast (by
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
        (fun i _ ↦ Nat.lcm_le_mul (hdpos i) (hepos i)))
  have hall : ∏ i, Nat.lcm (d i) (e i) = ∏ i ∈ Finset.univ.erase m, Nat.lcm (d i) (e i) := by
    rw [← Finset.mul_prod_erase Finset.univ
      (fun i ↦ Nat.lcm (d i) (e i)) (Finset.mem_univ m), hdm, hem]
    simp
  unfold PrimeGaps.qMod
  rw [Nat.cast_mul, hall]
  calc
    (PrimeGaps.sieveModulus N : ℝ) * ((∏ i ∈ Finset.univ.erase m,
          Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤ (PrimeGaps.sieveModulus N : ℝ) *
            PrimeGaps.sieveTruncation N δ θ ^ (2 : ℝ) :=
      mul_le_mul_of_nonneg_left hlcm (by positivity)
    _ = (PrimeGaps.sieveModulus N : ℝ) * ((N : ℝ) ^ (θ / 2 - δ)) ^ 2 := by
      rw [PrimeGaps.sieveTruncation, Real.rpow_two]
    _ < (N : ℝ) ^ θ := hWR

/-- Ordinary-BV error for the corrected retained square, normalized
directly by `Fmax`.  The `(log N)^k` pointwise divisor-weight cost is
absorbed by requesting exponent `A + 2k` from the same standing level of
distribution hypothesis. -/
theorem retained_twoWeightError_bound_Fmax {k : ℕ} (hk : 2 ≤ k) (m : Fin k) (A : ℝ) (hA : 0 < A)
    (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m
          (⇑(retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) ≤ C *
                MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
            (N : ℝ) / Real.log N ^ A := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < 1 := hθ.2
  obtain ⟨hΘ, hΔ⟩ := aux_params_mem hε hθ hδ hεθ
  obtain ⟨Clam, Nlam, hClam, hlamBound⟩ := lambdaRetained_abs_le_Fmax_log hk ε hε F hF hFsupp
      θ δ hθ hδ hεθ m
  obtain ⟨C₃, N₃, hC₃, hcollapse⟩ := MaynardS2Error.collapse_to_modulus_sum_of_pair_bound_with_bound
      (k := k) (by omega)
      (auxTheta δ θ ε) (auxDelta δ θ ε) θ
  obtain ⟨C₄, N₄, hC₄, hLoDsum⟩ := MaynardS2Error.weighted_modulus_sum_bound (k := k)
      θ hθ0 hθ1 hBV (A + 2 * k) (by
        have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith)
  obtain ⟨NW, hWR⟩ := MaynardS2Error.primorial_D0_Rsq_lt_Npow (θ := θ) (δ := δ) hδ.1
  refine ⟨4 * C₃ * Clam ^ 2 * C₄, max (max (max Nlam N₃) N₄) (max NW (rexp 1)),
    by positivity, ?_⟩
  intro N hN
  have hNlam : Nlam ≤ (N : ℝ) := le_trans (le_trans (le_trans (le_max_left _ _)
      (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₃ : N₃ ≤ (N : ℝ) := le_trans (le_trans (le_trans (le_max_right _ _)
      (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₄ : N₄ ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNW : NW ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNe : rexp 1 ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : (1 : ℝ) ≤ N := by
    exact le_trans (by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith) hNe
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  let Lret := retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
    ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
      ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
  let wRet : MaynardS2Error.SieveWeights k (N : ℝ) (auxTheta δ θ ε) (auxDelta δ θ ε) :=
    combinedWeight (⇑Lret) (⇑Lret) (lambdaRetained_epsPermissible k N δ θ ε m F)
      (lambdaRetained_epsPermissible k N δ θ ε m F)
  let B : ℝ := 2 * Clam * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k
  have hB : ∀ d, |wRet.lam d| ≤ B := by
    intro d
    have hd := hlamBound N hNlam d
    dsimp [wRet, B]
    calc |(|Lret d| + |Lret d|)|
        = 2 * |Lret d| := by
          rw [abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
          ring
      _ ≤ 2 * (Clam * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k) :=
        mul_le_mul_of_nonneg_left hd (by norm_num)
      _ = 2 * Clam * MaynardSmoothY.Fmax (Grescale ε F) *
          Real.log N ^ k := by ring
  let gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop := fun d e ↦
    d m = 1 ∧ e m = 1 ∧ Lret d ≠ 0 ∧ Lret e ≠ 0
  letI : DecidableRel gate := Classical.decRel _
  have hmod : ∀ d e, gate d e → wRet.lam d ≠ 0 → wRet.lam e ≠ 0 →
      (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e : ℝ) < (N : ℝ) ^ θ := by
    intro d e hg _ _
    have hdpos : ∀ i, 0 < d i := fun i ↦ Nat.lt_of_lt_of_le Nat.zero_lt_one
      ((epsPermissible_conditions (lambdaRetained_epsPermissible k N δ θ ε m F) hg.2.2.1).1 i)
    have hepos : ∀ i, 0 < e i := fun i ↦ Nat.lt_of_lt_of_le Nat.zero_lt_one
      ((epsPermissible_conditions (lambdaRetained_epsPermissible k N δ θ ε m F) hg.2.2.2).1 i)
    refine qMod_lt_Npow_of_outer_le m hdpos hepos hg.1 hg.2.1 ?_ (hWR (N : ℝ) hNW)
    calc
      (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) * (∏ i ∈ Finset.univ.erase m, (e i : ℝ)) ≤
          PrimeGaps.sieveTruncation N δ θ ^ (1 - ε) * PrimeGaps.sieveTruncation N δ θ ^ (1 - ε) :=
        mul_le_mul
          (retainedL_outer_support ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
              ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) d hg.2.2.1)
          (retainedL_outer_support ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
              ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) e hg.2.2.2)
          (by positivity) (by positivity)
      _ = PrimeGaps.sieveTruncation N δ θ ^ (2 * (1 - ε)) := by
        rw [← Real.rpow_add (by positivity)]
        congr 1
        ring
      _ ≤ PrimeGaps.sieveTruncation N δ θ ^ (2 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le
        · unfold PrimeGaps.sieveTruncation
          exact Real.one_le_rpow hN1 (by linarith [hδ.2])
        · linarith
  have hcol := hcollapse (N : ℝ) hN₃ wRet B hB (N : ℝ) (PrimeGaps.sieveModulus N)
    PrimeGaps.W_pos (fun d hd ↦ (Finset.mem_permissibleSupport_iff.mp
        (wRet.support (Finsupp.mem_support_iff.mpr hd))).2.1) gate hmod
  have hdom : PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m (⇑Lret) (⇑Lret) ≤
      MaynardS2Error.gatedErrorContribution (N : ℝ) (PrimeGaps.sieveModulus N)
        wRet.lam gate := by
    convert twoWeightError_le_totalError m (⇑Lret) (⇑Lret)
      (lambdaRetained_epsPermissible k N δ θ ε m F)
      (lambdaRetained_epsPermissible k N δ θ ε m F) using 1
    simp [gate, wRet, MaynardS2Error.gatedErrorContribution]
  let Sq := ∑ q ∈ {q ∈ Finset.range (⌊(N : ℝ) ^ θ⌋₊ + 1) | 1 ≤ q},
      (τ (3 * k) q : ℝ) ^ 2 * MaynardS2Error.windowError (N : ℝ) q
  have h2 := hLoDsum (N : ℝ) hN₄
  change Sq ≤ C₄ * (N : ℝ) / Real.log N ^ (A + 2 * (k : ℝ)) at h2
  have hmul : 0 ≤ C₃ * B ^ 2 := by positivity
  have hchain : PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m (⇑Lret) (⇑Lret) ≤
      C₃ * B ^ 2 * (C₄ * (N : ℝ) / Real.log N ^ (A + 2 * (k : ℝ))) :=
    hdom.trans (hcol.trans (mul_le_mul_of_nonneg_left h2 hmul))
  have hLpos : 0 < Real.log N := Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) hNe)
  have hpow2 : ((Real.log N ^ k) ^ 2 : ℝ) = Real.log N ^ (2 * (k : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast (Real.log N) (k * 2)]
    congr 1
    push_cast
    ring
  have hsplit : Real.log N ^ (A + 2 * (k : ℝ)) = Real.log N ^ A * Real.log N ^ (2 * (k : ℝ)) :=
    Real.rpow_add hLpos A _
  dsimp [B, Lret] at hchain ⊢
  have hBsq : (2 * Clam * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k) ^ 2 =
      4 * Clam ^ 2 * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (Real.log N ^ k) ^ 2 := by
    ring
  have hconst : C₃ * (2 * Clam * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k) ^ 2 *
      (C₄ * (N : ℝ) / Real.log N ^ (A + 2 * (k : ℝ))) = 4 * C₃ * Clam ^ 2 * C₄ *
        MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ A := by
    rw [hBsq, hpow2, hsplit]
    field_simp
  rwa [hconst] at hchain

/-- Ordinary-BV error for the mixed retained/discarded form with outer support `R²`. -/
theorem mixed_twoWeightError_bound_Fmax {k : ℕ} (hk : 2 ≤ k) (m : Fin k) (A : ℝ) (hA : 0 < A)
    (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m
          (⇑(retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) ≤ C *
                MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
            (N : ℝ) / Real.log N ^ A := by
  have hθ0 : 0 < θ := hθ.1
  have hθ1 : θ < 1 := hθ.2
  obtain ⟨Cr, Nr, hCr, hrBound⟩ := lambdaRetained_abs_le_Fmax_log hk ε hε F hF hFsupp
      θ δ hθ hδ hεθ m
  obtain ⟨Cd, Nd, hCd, hdBound⟩ := lambdaDiscarded_abs_le_Fmax_log hk ε hε F hF hFsupp
      θ δ hθ hδ hεθ m
  obtain ⟨C₃, N₃, hC₃, hcollapse⟩ := MaynardS2Error.collapse_to_modulus_sum_of_pair_bound_with_bound
      (k := k) (by omega)
      (auxTheta δ θ ε) (auxDelta δ θ ε) θ
  obtain ⟨C₄, N₄, hC₄, hLoDsum⟩ := MaynardS2Error.weighted_modulus_sum_bound (k := k)
      θ hθ0 hθ1 hBV (A + 2 * k) (by
        have hkR : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith)
  obtain ⟨NW, hWR⟩ := MaynardS2Error.primorial_D0_Rsq_lt_Npow (θ := θ) (δ := δ) hδ.1
  refine ⟨C₃ * (Cr + Cd) ^ 2 * C₄, max (max (max (max Nr Nd) N₃) N₄) (max NW (rexp 1)),
    by positivity, ?_⟩
  intro N hN
  simp only [max_le_iff] at hN
  obtain ⟨⟨⟨⟨hNr, hNd⟩, hN₃⟩, hN₄⟩, hNW, hNe⟩ := hN
  have hN1 : (1 : ℝ) ≤ N := by
    exact le_trans (by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith) hNe
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  let Lret := retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
    ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
      ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
  let Ldisc := discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
    ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
      ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))
  let wMix : MaynardS2Error.SieveWeights k (N : ℝ) (auxTheta δ θ ε) (auxDelta δ θ ε) :=
    combinedWeight (⇑Lret) (⇑Ldisc) (lambdaRetained_epsPermissible k N δ θ ε m F)
      (lambdaDiscarded_epsPermissible k N δ θ ε m F)
  let B : ℝ := (Cr + Cd) * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k
  have hB : ∀ d, |wMix.lam d| ≤ B := by
    intro d
    have hr := hrBound N hNr d
    have hd := hdBound N hNd d
    have hw : wMix.lam d = |Lret d| + |Ldisc d| := rfl
    rw [hw, abs_of_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))]
    calc |Lret d| + |Ldisc d|
        ≤ Cr * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k +
              Cd * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k := add_le_add hr hd
      _ = B := by dsimp [B]; ring
  let gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop := fun d e ↦
    d m = 1 ∧ e m = 1 ∧ Lret d ≠ 0 ∧ Ldisc e ≠ 0
  letI : DecidableRel gate := Classical.decRel _
  have hmod : ∀ d e, gate d e → wMix.lam d ≠ 0 → wMix.lam e ≠ 0 →
      (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e : ℝ) < (N : ℝ) ^ θ := by
    intro d e hg _ _
    have hdpos : ∀ i, 0 < d i := fun i ↦ Nat.lt_of_lt_of_le Nat.zero_lt_one
      ((epsPermissible_conditions (lambdaRetained_epsPermissible k N δ θ ε m F) hg.2.2.1).1 i)
    have hepos : ∀ i, 0 < e i := fun i ↦ Nat.lt_of_lt_of_le Nat.zero_lt_one
      ((epsPermissible_conditions (lambdaDiscarded_epsPermissible k N δ θ ε m F) hg.2.2.2).1 i)
    have hlcm : ((∏ i ∈ Finset.univ.erase m,
            Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤ PrimeGaps.sieveTruncation N δ θ ^ (2 : ℝ) :=
      calc
        ((∏ i ∈ Finset.univ.erase m,
            Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤ (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) *
                (∏ i ∈ Finset.univ.erase m, (e i : ℝ)) := by
              exact_mod_cast (by
                rw [← Finset.prod_mul_distrib]
                exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
                  (fun i _ ↦ Nat.lcm_le_mul (hdpos i) (hepos i)))
        _ ≤ PrimeGaps.sieveTruncation N δ θ ^ (1 - ε) * PrimeGaps.sieveTruncation N δ θ ^ (1 + ε) :=
          mul_le_mul (retainedL_outer_support ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
              ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))) d hg.2.2.1)
            (lambdaDiscarded_outer_support_enlarged k N δ θ ε m F e hg.2.2.2)
            (by positivity) (by positivity)
        _ = PrimeGaps.sieveTruncation N δ θ ^ (2 : ℝ) := by
          rw [← Real.rpow_add (by positivity)]
          congr 1
          ring
    have hall : ∏ i, Nat.lcm (d i) (e i) = ∏ i ∈ Finset.univ.erase m, Nat.lcm (d i) (e i) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ Nat.lcm (d i) (e i)) (Finset.mem_univ m),
        hg.1, hg.2.1]
      simp
    unfold PrimeGaps.qMod
    rw [Nat.cast_mul, hall]
    calc
      (PrimeGaps.sieveModulus N : ℝ) * ((∏ i ∈ Finset.univ.erase m,
            Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤ (PrimeGaps.sieveModulus N : ℝ) *
              PrimeGaps.sieveTruncation N δ θ ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left hlcm (by positivity)
      _ = (PrimeGaps.sieveModulus N : ℝ) *
          ((N : ℝ) ^ (θ / 2 - δ)) ^ 2 := by
        rw [PrimeGaps.sieveTruncation, Real.rpow_two]
      _ < (N : ℝ) ^ θ := hWR (N : ℝ) hNW
  have hcol := hcollapse (N : ℝ) hN₃ wMix B hB (N : ℝ) (PrimeGaps.sieveModulus N)
    PrimeGaps.W_pos (fun d hd ↦ (Finset.mem_permissibleSupport_iff.mp
        (wMix.support (Finsupp.mem_support_iff.mpr hd))).2.1) gate hmod
  have hdom : PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m (⇑Lret) (⇑Ldisc) ≤
      MaynardS2Error.gatedErrorContribution (N : ℝ) (PrimeGaps.sieveModulus N)
        wMix.lam gate := by
    convert twoWeightError_le_totalError m (⇑Lret) (⇑Ldisc)
      (lambdaRetained_epsPermissible k N δ θ ε m F)
      (lambdaDiscarded_epsPermissible k N δ θ ε m F) using 1
    simp [gate, wMix, MaynardS2Error.gatedErrorContribution]
  let Sq := ∑ q ∈ {q ∈ Finset.range (⌊(N : ℝ) ^ θ⌋₊ + 1) | 1 ≤ q},
      (τ (3 * k) q : ℝ) ^ 2 * MaynardS2Error.windowError (N : ℝ) q
  have h2 := hLoDsum (N : ℝ) hN₄
  change Sq ≤ C₄ * (N : ℝ) / Real.log N ^ (A + 2 * (k : ℝ)) at h2
  have hmul : 0 ≤ C₃ * B ^ 2 := by positivity
  have hchain : PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m (⇑Lret) (⇑Ldisc) ≤
      C₃ * B ^ 2 * (C₄ * (N : ℝ) / Real.log N ^ (A + 2 * (k : ℝ))) :=
    hdom.trans (hcol.trans (mul_le_mul_of_nonneg_left h2 hmul))
  have hLpos : 0 < Real.log N := Real.log_pos (lt_of_lt_of_le (Real.one_lt_exp_iff.mpr one_pos) hNe)
  have hpow2 : ((Real.log N ^ k) ^ 2 : ℝ) = Real.log N ^ (2 * (k : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast (Real.log N) (k * 2)]
    congr 1
    push_cast
    ring
  have hsplit : Real.log N ^ (A + 2 * (k : ℝ)) = Real.log N ^ A * Real.log N ^ (2 * (k : ℝ)) :=
    Real.rpow_add hLpos A _
  dsimp [B, Lret, Ldisc] at hchain ⊢
  rw [show
      C₃ * ((Cr + Cd) * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k) ^ 2 *
          (C₄ * (N : ℝ) / Real.log N ^ (A + 2 * (k : ℝ))) = C₃ * (Cr + Cd) ^ 2 * C₄ *
            MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
            (N : ℝ) / Real.log N ^ A by
      rw [show ((Cr + Cd) * MaynardSmoothY.Fmax (Grescale ε F) * Real.log N ^ k) ^ 2 =
          (Cr + Cd) ^ 2 * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 *
            (Real.log N ^ k) ^ 2 by ring,
        hpow2, hsplit]
      field_simp] at hchain
  exact hchain

/-- BV substitution for the retained/discarded bilinear prime sum in the smooth norm. -/
theorem corrected_bilinearPrimeSum_substitute_weak_Fmax {k : ℕ}
    (hk : 2 ≤ k) (h : Fin k → ℕ) (hinj : Function.Injective h)
    (m : Fin k) (A : ℝ) (hA : 0 < A)
    (ε : ℝ) (hε : 0 ≤ ε)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1)
    (hθ' : θ < 1 / 2)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (PrimeGaps.sieveModulus N),
        (∀ i, ((w₀.val : ℤ) + (h i : ℤ)).gcd (PrimeGaps.sieveModulus N) = 1) →
      |PrimeGaps.bilinearPrimeSum h N m (⇑(retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) w₀ -
                (Nat.primeCountingIoc N (2 * N) : ℝ) /
            (PrimeGaps.sieveModulus N).totient *
              PrimeGaps.restrictedCrossSum h m (PrimeGaps.sieveModulus N)
                (⇑(retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
                  ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                    ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
                (⇑(discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
                  ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
                    ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))| ≤
        C * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ A := by
  obtain ⟨Ccrt, hCcrt, Ncrt, hcrt⟩ := corrected_bilinearPrimeSum_crt_weak h hinj m ε hε F
      θ δ hθ hδ hεθ
  obtain ⟨Cbv, Nbv, hCbv, hbv⟩ := mixed_twoWeightError_bound_Fmax hk m A hA ε hε
      F hF hFsupp θ δ hθ hθ' hBV hδ hεθ
  refine ⟨Ccrt * Cbv, by positivity, max Ncrt Nbv, ?_⟩
  intro N hN w₀ hw₀
  simp only [max_le_iff] at hN
  obtain ⟨hNcrt, hNbv⟩ := hN
  have hc := hcrt N hNcrt w₀ hw₀
  have hb := hbv N hNbv
  calc _
      ≤ Ccrt * PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m
          (⇑(retainedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))))
          (⇑(discardedL ((PrimeGaps.sieveTruncation N δ θ) ^ (1 -
            ε)) m (PrimeGaps.l₀ ((PrimeGaps.sieveTruncation N δ θ) ^ (1 +
              ε)) (PrimeGaps.sieveModulus N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x))))) := hc
    _ ≤ Ccrt * (Cbv * MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ A) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = Ccrt * Cbv *
        MaynardSmoothY.Fmax (Grescale ε F) ^ 2 * (N : ℝ) / Real.log N ^ A := by ring


end Gaps246
