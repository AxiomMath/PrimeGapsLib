/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Gap246.Sieve.S1
public import PrimeGapsTheory.Sieve.S2m.Bilinear

/-!
# Bilinear errors for the enlarged sieve

Bombieri--Vinogradov estimates for bilinear forms whose weights have enlarged permissible
support.

## Main results

* `lem_bv_modulus`: Bounds the two-weight error under split support conditions.
* `lem_retained`: Bounds the retained-square and mixed errors.
-/

@[expose] public section

open Real

open Finset
open scoped ArithmeticFunction BigOperators

namespace Gaps246

open ArithmeticFunction zeta

/-- Transfer enlarged support to any sieve parameters with the same truncation exponent. -/
theorem epsPermissible_permissibleSupport_of_exponent_eq
    {k N : ℕ} {δ θ ε Θ Δ : ℝ} {lam : (Fin k → ℕ) → ℝ}
    (hp : epsPermissible k N δ θ ε lam)
    (hexp : Θ / 2 - Δ = (θ / 2 - δ) * (1 + ε))
    {d : Fin k → ℕ} (hd : lam d ≠ 0) :
    d ∈ Finset.permissibleSupport k ⌊(N : ℝ) ^ (Θ / 2 - Δ)⌋₊
      (PrimeGaps.sieveModulus N) := by
  obtain ⟨hpos, hprod, hcop, hsq⟩ := epsPermissible_conditions hp hd
  rw [Finset.mem_permissibleSupport_iff']
  refine ⟨fun i ↦ Nat.one_le_iff_ne_zero.mp (hpos i), ?_, hcop, hsq⟩
  apply Nat.le_floor
  rw [hexp]
  calc ((∏ i, d i : ℕ) : ℝ)
      ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := by
        simpa [Nat.cast_prod] using hprod
    _ = (↑N : ℝ) ^ ((θ / 2 - δ) * (1 + ε)) := by
      simp only [PrimeGaps.sieveTruncation]
      rw [← Real.rpow_mul (Nat.cast_nonneg N)]

/-- For two enlarged permissible weights, bundle the pointwise sum `|λ| + |λ'|` at the
auxiliary truncation parameters. -/
noncomputable def combinedWeight {k N : ℕ} {δ θ ε : ℝ} (lam lam' : (Fin k → ℕ) → ℝ)
    (hp : epsPermissible k N δ θ ε lam) (hp' : epsPermissible k N δ θ ε lam') :
    MaynardS2Error.SieveWeights k (↑N : ℝ) (auxTheta δ θ ε) (auxDelta δ θ ε) where
  lam := Finsupp.onFinset (Finset.permissibleSupport k ⌊(N : ℝ) ^
      (auxTheta δ θ ε / 2 - auxDelta δ θ ε)⌋₊ (PrimeGaps.sieveModulus N))
    (fun d ↦ |lam d| + |lam' d|) (by
    intro d hd
    rcases eq_or_ne (lam d) 0 with h | h
    · rcases eq_or_ne (lam' d) 0 with h' | h'
      · exact absurd (by rw [h, h']; simp) hd
      · exact epsPermissible_permissibleSupport_of_exponent_eq hp'
          (by rw [aux_exponent]; ring) h'
    · exact epsPermissible_permissibleSupport_of_exponent_eq hp
        (by rw [aux_exponent]; ring) h)
  support := Finsupp.support_onFinset_subset


/-- The two-weight bilinear error is dominated by the gated error of `|λ| + |λ'|`. -/
theorem twoWeightError_le_totalError {k N : ℕ} {δ θ ε : ℝ} (m : Fin k) (lam lam' : (Fin k → ℕ) → ℝ)
    (hp : epsPermissible k N δ θ ε lam) (hp' : epsPermissible k N δ θ ε lam') :
    PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m lam lam' ≤
      MaynardS2Error.gatedErrorContribution (N : ℝ) (PrimeGaps.sieveModulus N)
        (combinedWeight lam lam' hp hp').lam
        (fun d e ↦ d m = 1 ∧ e m = 1 ∧ lam d ≠ 0 ∧ lam' e ≠ 0) := by
  set w := combinedWeight lam lam' hp hp' with hwdef
  have hwlam : ∀ d, w.lam d = |lam d| + |lam' d| := fun d ↦ rfl
  set D := (MaynardS2Error.totalErrorContribution_finite_support w).toFinset with hDdef
  have hmemD : ∀ d, w.lam d ≠ 0 → d ∈ D := by
    intro d hd
    rwa [hDdef, Set.Finite.mem_toFinset]
  have hlamD : ∀ d, lam d ≠ 0 → d ∈ D := by
    intro d hd
    refine hmemD d ?_
    rw [hwlam d]
    have : (0 : ℝ) < |lam d| + |lam' d| := by
      have := abs_pos.mpr hd; positivity
    linarith
  have hlamD' : ∀ d, lam' d ≠ 0 → d ∈ D := by
    intro d hd
    refine hmemD d ?_
    rw [hwlam d]
    have : (0 : ℝ) < |lam d| + |lam' d| := by
      have := abs_pos.mpr hd; positivity
    linarith
  have hEnn : ∀ d e : Fin k → ℕ, 0 ≤ MaynardS2Error.windowError (↑N : ℝ)
        (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e) :=
    fun d e ↦ MaynardS2Error.windowError_nonneg _ _
  set G : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦ if d m = 1 ∧ e m = 1 ∧ lam d * lam' e ≠ 0 then
      |lam d| * |lam' e| *
        MaynardS2Error.windowError (↑N : ℝ) (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e)
    else 0 with hGdef
  set F : (Fin k → ℕ) → (Fin k → ℕ) → ℝ := fun d e ↦
    if (d m = 1 ∧ e m = 1 ∧ lam d ≠ 0 ∧ lam' e ≠ 0) ∧ w.lam d * w.lam e ≠ 0 then
      |w.lam d| * |w.lam e| *
        MaynardS2Error.windowError (↑N : ℝ) (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e)
    else 0 with hFdef
  have hGe0 : ∀ d e, e ∉ D → G d e = 0 := by
    intro d e he
    have hz : lam' e = 0 := by by_contra h; exact he (hlamD' e h)
    simp only [hGdef]; rw [if_neg (by rw [hz]; simp)]
  have hGd0 : ∀ d e, d ∉ D → G d e = 0 := by
    intro d e hd
    have hz : lam d = 0 := by by_contra h; exact hd (hlamD d h)
    simp only [hGdef]; rw [if_neg (by rw [hz]; simp)]
  have hGinner : ∀ d, (∑' e, G d e) = ∑ e ∈ D, G d e := fun d ↦ tsum_eq_sum (fun e he ↦ hGe0 d e he)
  have hGouter : PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m lam lam' =
        ∑ d ∈ D, ∑ e ∈ D, G d e := by
    rw [PrimeGaps.twoWeightError]
    have : (∑' d, ∑' e, G d e) = ∑ d ∈ D, ∑ e ∈ D, G d e := by
      rw [tsum_eq_sum (s := D) (fun d hd ↦ by
        rw [hGinner d]; exact Finset.sum_eq_zero (fun e _ ↦ hGd0 d e hd))]
      exact Finset.sum_congr rfl (fun d _ ↦ hGinner d)
    exact this
  have hFe0 : ∀ d e, e ∉ D → F d e = 0 := by
    intro d e he
    have hz : w.lam e = 0 := by by_contra h; exact he (hmemD e h)
    simp only [hFdef]; rw [if_neg (by rw [hz]; simp)]
  have hFd0 : ∀ d e, d ∉ D → F d e = 0 := by
    intro d e hd
    have hz : w.lam d = 0 := by by_contra h; exact hd (hmemD d h)
    simp only [hFdef]; rw [if_neg (by rw [hz]; simp)]
  have hFinner : ∀ d, (∑' e, F d e) = ∑ e ∈ D, F d e := fun d ↦ tsum_eq_sum (fun e he ↦ hFe0 d e he)
  have hFouter : MaynardS2Error.gatedErrorContribution (N : ℝ) (PrimeGaps.sieveModulus N) w.lam
      (fun d e ↦ d m = 1 ∧ e m = 1 ∧ lam d ≠ 0 ∧ lam' e ≠ 0) = ∑ d ∈ D, ∑ e ∈ D, F d e := by
    rw [MaynardS2Error.gatedErrorContribution]
    have : (∑' d, ∑' e, F d e) = ∑ d ∈ D, ∑ e ∈ D, F d e := by
      rw [tsum_eq_sum (s := D) (fun d hd ↦ by
        rw [hFinner d]; exact Finset.sum_eq_zero (fun e _ ↦ hFd0 d e hd))]
      exact Finset.sum_congr rfl (fun d _ ↦ hFinner d)
    exact this
  have hGF : ∀ d e, G d e ≤ F d e := by
    intro d e
    simp only [hGdef, hFdef]
    by_cases hc : d m = 1 ∧ e m = 1 ∧ lam d * lam' e ≠ 0
    · rw [if_pos hc]
      have hd0 : lam d ≠ 0 := fun h ↦ hc.2.2 (by rw [h]; ring)
      have he0 : lam' e ≠ 0 := fun h ↦ hc.2.2 (by rw [h]; ring)
      have hwd : w.lam d ≠ 0 := by
        rw [hwlam d]; have := abs_pos.mpr hd0; positivity
      have hwe : w.lam e ≠ 0 := by
        rw [hwlam e]; have := abs_pos.mpr he0; positivity
      rw [if_pos ⟨⟨hc.1, hc.2.1, hd0, he0⟩, mul_ne_zero hwd hwe⟩]
      have hle_d : |lam d| ≤ |w.lam d| := by
        rw [hwlam d, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |lam d| + |lam' d|)]
        exact le_add_of_nonneg_right (abs_nonneg _)
      have hle_e : |lam' e| ≤ |w.lam e| := by
        rw [hwlam e, abs_of_nonneg (by positivity : (0 : ℝ) ≤ |lam e| + |lam' e|)]
        exact le_add_of_nonneg_left (abs_nonneg _)
      have hE := hEnn d e
      have h1 : |lam d| * |lam' e| ≤ |w.lam d| * |w.lam e| :=
        mul_le_mul hle_d hle_e (abs_nonneg _) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_right h1 hE
    · rw [if_neg hc]
      split_ifs with hc2
      · exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hEnn d e)
      · exact le_refl _
  rw [hGouter, hFouter]
  exact Finset.sum_le_sum (fun d _ ↦ Finset.sum_le_sum (fun e _ ↦ hGF d e))

/-- Fix `m`.  For `ε`-permissible weights `λ, λ'` additionally
supported on `{∏_{i≠m} dᵢ ≤ R^a}`, `{∏_{i≠m} dᵢ ≤ R^b}` with `a + b ≤ 2`, the
aggregate error of the retained bilinear form
`∑_n χ_ℙ(n+h_m) ∑_{d,e} λ_d λ'_e ∏_i 𝟙[[dᵢ,eᵢ] ∣ n+hᵢ]` — encoded as
`twoWeightError` — is `O_A(N / (log N)^A)` for every `A > 0`. -/
theorem lem_bv_modulus (k : ℕ) (hk : 2 ≤ k) (m : Fin k) (A : ℝ) (hA : 0 < A)
    (θ δ ε : ℝ) (hε : 0 ≤ ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) (hθ : θ < 1 / 2)
    (hεθ : 1 + ε < 1 / θ)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1)
    (a b : ℝ) (hab : a + b ≤ 2) :
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ (↑N : ℝ) → ∀ (lam lam' : (Fin k → ℕ) → ℝ)
        (hp : epsPermissible k N δ θ ε lam) (hp' : epsPermissible k N δ θ ε lam'),
        (∀ d, lam d ≠ 0 →
            (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ a) →
        (∀ d, lam' d ≠ 0 →
            (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ b) →
        PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m lam lam' ≤
          C * (PrimeGaps.lToY (combinedWeight lam lam' hp hp').lam).maxRealAbs ^ 2 *
              (↑N : ℝ) / (Real.log ↑N) ^ A := by
  have hθ0 : 0 < θ := by linarith [hδ.1, hδ.2]
  have hθ1 : θ < 1 := by linarith
  let Θ := auxTheta δ θ ε
  let Δ := auxDelta δ θ ε
  obtain ⟨hΘmem, hΔmem⟩ := aux_params_mem hε ⟨hθ0, hθ1⟩ hδ hεθ
  obtain ⟨C₁, N₁, hC₁, hlam⟩ := MaynardS2Error.lambdaMax_bound k hk Θ Δ hΔmem.1 hΔmem.2 hΘmem.2
  obtain ⟨C₃, N₃, hC₃, hcollapse⟩ :=
    MaynardS2Error.collapse_to_modulus_sum_of_pair_bound (k := k) (by omega)
      Θ Δ θ C₁ N₁ hlam
  obtain ⟨C₄, N₄, hC₄, hLoDsum⟩ := MaynardS2Error.weighted_modulus_sum_bound (k := k) θ hθ0 hθ1 hBV
      (A + 2 * k) (by
        have h2k : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
        linarith)
  obtain ⟨NW, hWR⟩ := MaynardS2Error.primorial_D0_Rsq_lt_Npow (θ := θ) (δ := δ) hδ.1
  refine ⟨C₃ * C₁ ^ 2 * C₄,
    max (max (max N₁ N₃) N₄) (max NW (rexp 1)), by positivity, ?_⟩
  intro N hN lam lam' hp hp' hsa hsb
  have hN₁ : N₁ ≤ (N : ℝ) :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₃ : N₃ ≤ (N : ℝ) :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_left _ _)) hN
  have hN₄ : N₄ ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNW : NW ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNe : rexp 1 ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1 : (1 : ℝ) ≤ N := by exact le_trans (by have := Real.add_one_le_exp (1 : ℝ); linarith) hNe
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le one_pos hN1
  let wAux : MaynardS2Error.SieveWeights k (N : ℝ) Θ Δ := combinedWeight lam lam' hp hp'
  let gate : (Fin k → ℕ) → (Fin k → ℕ) → Prop := fun d e ↦
    d m = 1 ∧ e m = 1 ∧ lam d ≠ 0 ∧ lam' e ≠ 0
  letI : DecidableRel gate := Classical.decRel _
  have hmod : ∀ d e, gate d e → wAux.lam d ≠ 0 → wAux.lam e ≠ 0 →
      (PrimeGaps.qMod (PrimeGaps.sieveModulus N) d e : ℝ) < (N : ℝ) ^ θ := by
    intro d e hg _ _
    have hdpos : ∀ i, 0 < d i := by
      have hc : (∀ i, 1 ≤ d i) ∧ ((∏ i, d i : ℝ) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) ∧
            Nat.Coprime (∏ i, d i) (PrimeGaps.sieveModulus N) ∧ Squarefree (∏ i, d i) := by
        by_contra hc
        exact hg.2.2.1 (hp d hc)
      exact fun i ↦ Nat.lt_of_lt_of_le Nat.zero_lt_one (hc.1 i)
    have hepos : ∀ i, 0 < e i := by
      have hc : (∀ i, 1 ≤ e i) ∧ ((∏ i, e i : ℝ) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) ∧
            Nat.Coprime (∏ i, e i) (PrimeGaps.sieveModulus N) ∧ Squarefree (∏ i, e i) := by
        by_contra hc
        exact hg.2.2.2 (hp' e hc)
      exact fun i ↦ Nat.lt_of_lt_of_le Nat.zero_lt_one (hc.1 i)
    have hlcm_outer : ((∏ i ∈ Finset.univ.erase m, Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤
          (PrimeGaps.sieveTruncation N δ θ) ^ (a + b) := by
      have hlcm : ((∏ i ∈ Finset.univ.erase m, Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤
            (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) *
              (∏ i ∈ Finset.univ.erase m, (e i : ℝ)) := by
        exact_mod_cast (by
          rw [← Finset.prod_mul_distrib]
          exact Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _)
            (fun i _ ↦ Nat.lcm_le_mul (hdpos i) (hepos i)))
      calc
        ((∏ i ∈ Finset.univ.erase m, Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤
            (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) * (∏ i ∈ Finset.univ.erase m, (e i : ℝ)) := hlcm
        _ ≤ (PrimeGaps.sieveTruncation N δ θ) ^ a * (PrimeGaps.sieveTruncation N δ θ) ^ b :=
          mul_le_mul (hsa d hg.2.2.1) (hsb e hg.2.2.2) (by positivity) (by positivity)
        _ = (PrimeGaps.sieveTruncation N δ θ) ^ (a + b) := by
          rw [← Real.rpow_add (by positivity)]
    have hR1 : 1 ≤ PrimeGaps.sieveTruncation N δ θ := by
      unfold PrimeGaps.sieveTruncation
      exact Real.one_le_rpow hN1 (by linarith [hδ.2])
    have habpow :
        (PrimeGaps.sieveTruncation N δ θ) ^ (a + b) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (2 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hR1 hab
    have hall : ∏ i, Nat.lcm (d i) (e i) = ∏ i ∈ Finset.univ.erase m, Nat.lcm (d i) (e i) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ Nat.lcm (d i) (e i))
        (Finset.mem_univ m), hg.1, hg.2.1]
      simp
    unfold PrimeGaps.qMod
    rw [Nat.cast_mul, hall]
    calc
      (PrimeGaps.sieveModulus N : ℝ) * ((∏ i ∈ Finset.univ.erase m, Nat.lcm (d i) (e i) : ℕ) : ℝ) ≤
          (PrimeGaps.sieveModulus N : ℝ) * (PrimeGaps.sieveTruncation N δ θ) ^ (a + b) :=
        mul_le_mul_of_nonneg_left hlcm_outer (by positivity)
      _ ≤ (PrimeGaps.sieveModulus N : ℝ) * (PrimeGaps.sieveTruncation N δ θ) ^ (2 : ℝ) :=
        mul_le_mul_of_nonneg_left habpow (by positivity)
      _ = (PrimeGaps.sieveModulus N : ℝ) * ((N : ℝ) ^ (θ / 2 - δ)) ^ 2 := by
        rw [PrimeGaps.sieveTruncation, Real.rpow_two]
      _ < (N : ℝ) ^ θ := hWR (N : ℝ) hNW
  have hcol := hcollapse (N : ℝ) hN₃ wAux (N : ℝ) (PrimeGaps.sieveModulus N)
    PrimeGaps.W_pos (fun d hd ↦ (Finset.mem_permissibleSupport_iff.mp
        (wAux.support (Finsupp.mem_support_iff.mpr hd))).2.1) gate hmod
  have hdom : PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m lam lam' ≤
      MaynardS2Error.gatedErrorContribution (N : ℝ) (PrimeGaps.sieveModulus N)
        wAux.lam gate := by
    have hwAuxLam : wAux.lam = (combinedWeight lam lam' hp hp').lam := rfl
    rw [hwAuxLam]
    convert twoWeightError_le_totalError m lam lam' hp hp' using 1
    simp [gate, MaynardS2Error.gatedErrorContribution]
  have hL1 : (1 : ℝ) ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hNe
  have hLpos : (0 : ℝ) < Real.log N := lt_of_lt_of_le one_pos hL1
  set L := Real.log (N : ℝ) with hLdef
  set y := (PrimeGaps.lToY wAux.lam).maxRealAbs with hydef
  set Sq := ∑ q ∈ {q ∈ Finset.range (⌊(N : ℝ) ^ θ⌋₊ + 1) | 1 ≤ q},
      (τ (3 * k) q : ℝ) ^ 2 * MaynardS2Error.windowError (N : ℝ) q with hSqdef
  have h2 := hLoDsum (N : ℝ) hN₄
  change Sq ≤ C₄ * (N : ℝ) / L ^ (A + 2 * (k : ℝ)) at h2
  have hmul : 0 ≤ C₃ * (C₁ * y * L ^ k) ^ 2 := by positivity
  have hchain : PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m lam lam' ≤
      C₃ * (C₁ * y * L ^ k) ^ 2 * (C₄ * (N : ℝ) / L ^ (A + 2 * (k : ℝ))) :=
    le_trans hdom (le_trans hcol (mul_le_mul_of_nonneg_left h2 hmul))
  have hpow2 : ((L ^ k) ^ 2 : ℝ) = L ^ (2 * (k : ℝ)) := by
    rw [← pow_mul, ← Real.rpow_natCast L (k * 2)]
    congr 1
    push_cast
    ring
  have hsplit : L ^ (A + 2 * (k : ℝ)) = L ^ A * L ^ (2 * (k : ℝ)) := Real.rpow_add hLpos A _
  have hRHS : C₃ * (C₁ * y * L ^ k) ^ 2 *
      (C₄ * (N : ℝ) / L ^ (A + 2 * (k : ℝ))) = C₃ * C₁ ^ 2 * C₄ * y ^ 2 * (N : ℝ) / L ^ A := by
    have expand : (C₁ * y * L ^ k) ^ 2 = C₁ ^ 2 * y ^ 2 * (L ^ k) ^ 2 := by ring
    rw [expand, hpow2, hsplit]
    field_simp
  rw [hRHS] at hchain
  have hyEq : (PrimeGaps.lToY wAux.lam).maxRealAbs =
      (PrimeGaps.lToY (combinedWeight lam lam' hp hp').lam).maxRealAbs := by
    congr
  rw [hydef, hyEq] at hchain
  simpa [L] using hchain

/-- **`lem_retained`.**  For an `ε`-permissible source weight `λ₀` and the divisor-sum
split `λ = λ_{1,m} + λ_{2,m}` (`lambdaSplit1`/`lambdaSplit2`), the two retained sums
`∑_n χ_ℙ(n+h_m) A_{1,m}(n)²` and `∑_n χ_ℙ(n+h_m) A_{1,m}(n) A_{2,m}(n)` each have
aggregate error `O_A(N / (log N)^A)`.

The `A_{1,m}²` case uses the pair `(λ_{1,m}, λ_{1,m})` with `∏_{i≠m} dᵢ ≤ R^{1−ε}`
on both sides (`a + b = 2(1−ε) ≤ 2`); the `A_{1,m} A_{2,m}` case uses
`(λ_{1,m}, λ_{2,m})` with `R^{1−ε}` and `R^{1+ε}` (`a + b = 2`).  Both satisfy
`lem_bv_modulus`. -/
theorem lem_retained (k : ℕ) (hk : 2 ≤ k) (m : Fin k) (A : ℝ) (hA : 0 < A)
    (θ δ ε : ℝ) (hε : 0 ≤ ε) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) (hθ : θ < 1 / 2)
    (hεθ : 1 + ε < 1 / θ)
    (hBV : Nat.HasLevelOfDistribution Set.univ θ 1) :
    ∃ C₁ C₂ N₀ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ ∀ N : ℕ, N₀ ≤ (↑N : ℝ) →
      ∀ (lam0 : (Fin k → ℕ) → ℝ) (_ : epsPermissible k N δ θ ε lam0),
        (∀ (hp11 : epsPermissible k N δ θ ε (lambdaSplit1 k N δ θ ε m lam0)),
          PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m
            (lambdaSplit1 k N δ θ ε m lam0)
            (lambdaSplit1 k N δ θ ε m lam0) ≤ C₁ * (PrimeGaps.lToY
                (combinedWeight (lambdaSplit1 k N δ θ ε m lam0) (lambdaSplit1 k N δ θ ε m lam0)
                  hp11 hp11).lam).maxRealAbs ^ 2 * (↑N : ℝ) / (Real.log ↑N) ^ A) ∧
        (∀ (hp1 : epsPermissible k N δ θ ε (lambdaSplit1 k N δ θ ε m lam0))
           (hp2 : epsPermissible k N δ θ ε (lambdaSplit2 k N δ θ ε m lam0)),
          PrimeGaps.twoWeightError k (N : ℝ) (PrimeGaps.sieveModulus N) m
            (lambdaSplit1 k N δ θ ε m lam0)
            (lambdaSplit2 k N δ θ ε m lam0) ≤ C₂ * (PrimeGaps.lToY
                (combinedWeight (lambdaSplit1 k N δ θ ε m lam0) (lambdaSplit2 k N δ θ ε m lam0)
                  hp1 hp2).lam).maxRealAbs ^ 2 * (↑N : ℝ) / (Real.log ↑N) ^ A) := by
  obtain ⟨C₁, N₁, hC₁, hbv₁⟩ :=
    lem_bv_modulus k hk m A hA θ δ ε hε hδ hθ hεθ hBV (1 - ε) (1 - ε) (by linarith)
  obtain ⟨C₂, N₂, hC₂, hbv₂⟩ :=
    lem_bv_modulus k hk m A hA θ δ ε hε hδ hθ hεθ hBV (1 - ε) (1 + ε) (by linarith)
  refine ⟨C₁, C₂, max N₁ N₂, hC₁, hC₂, ?_⟩
  intro N hN lam0 hp0
  have hN₁ : N₁ ≤ (↑N : ℝ) := le_trans (le_max_left _ _) hN
  have hN₂ : N₂ ≤ (↑N : ℝ) := le_trans (le_max_right _ _) hN
  have hbound1 : ∀ d, lambdaSplit1 k N δ θ ε m lam0 d ≠ 0 →
      (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 - ε) := by
    intro d hd
    by_contra hlt
    exact hd (by simp only [lambdaSplit1]; rw [if_neg hlt, mul_zero])
  have hbound2 : ∀ d, lambdaSplit2 k N δ θ ε m lam0 d ≠ 0 →
      (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := by
    intro d hd
    have hlam0 : lam0 d ≠ 0 :=
      fun h ↦ hd (by simp only [lambdaSplit2, lambdaSplit1, h, zero_mul, sub_zero])
    have hcond : (∀ i, 1 ≤ d i) ∧ ((∏ i, d i : ℝ) ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε)) ∧
        Nat.Coprime (∏ i, d i) (PrimeGaps.sieveModulus N) ∧ Squarefree (∏ i, d i) := by
      by_contra hc; exact hlam0 (hp0 d hc)
    obtain ⟨h1, h2, _, _⟩ := hcond
    have hsub : (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ ∏ i, (d i : ℝ) := by
      rw [← Finset.mul_prod_erase Finset.univ (fun i ↦ (d i : ℝ)) (Finset.mem_univ m)]
      exact le_mul_of_one_le_left
        (Finset.prod_nonneg (fun i _ ↦ by positivity)) (by exact_mod_cast h1 m)
    calc (∏ i ∈ Finset.univ.erase m, (d i : ℝ)) ≤ ∏ i, (d i : ℝ) := hsub
      _ ≤ (PrimeGaps.sieveTruncation N δ θ) ^ (1 + ε) := h2
  refine ⟨?_, ?_⟩
  · intro hp11
    exact hbv₁ N hN₁ _ _ hp11 hp11 hbound1 hbound1
  · intro hp1 hp2
    exact hbv₂ N hN₂ _ _ hp1 hp2 hbound1 hbound2

end Gaps246
