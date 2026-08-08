/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.NumberTheory.Compatibility
public import PrimeGapsTheory.Endgame.MainProp
public import PrimeGapsTheory.Endgame.ManyPrimes
public import PrimeGapsTheory.Gap246.Sieve.S2

/-!
# The enlarged sieve witness

The first- and second-moment estimates imply positivity of the enlarged sieve sum and the
Maynard--Tao conclusion for an admissible tuple.

## Main results

* `enlarged_S_positive`: The enlarged sieve sum is eventually positive.
* `prop_witness`: A smooth enlarged witness yields infinitely many simultaneous primes.
-/

@[expose] public section

open Real

open scoped Topology

open Finset MeasureTheory GPYSieveS1 MaynardSmoothY Filter PrimeGaps
open scoped PrimeGaps PrimeGaps.sieveTruncation PrimeGaps.sieveModulus BigOperators

namespace Gaps246

theorem exists_fixedWidth_Jsum_margin {k : ℕ} (hk : 2 ≤ k) (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (c ρ Ival : ℝ)
    (hmargin : ρ * Ival < c * ∑ m : Fin k, jEps k ε m F) :
    ∃ q : ℕ, ρ * Ival < c * ∑ m : Fin k, (1 + ε) ^ (k + 1) * PrimeGaps.J m
          (PrimeGaps.retainedProfileLp (ε := ε) (η := (((q + 1 : ℕ) : ℝ)⁻¹)) m (Grescale ε F)
            (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) := by
  have ht := tendsto_fixedWidth_Jsum_to_jEps_sum
    hk ε hε hε1 F hF hFsupp
  have htc := ht.const_mul c
  have hev : ∀ᶠ q : ℕ in Filter.atTop, ρ * Ival < c * ∑ m : Fin k, (1 + ε) ^ (k + 1) * PrimeGaps.J m
          (PrimeGaps.retainedProfileLp (ε := ε) (η := (((q + 1 : ℕ) : ℝ)⁻¹)) m (Grescale ε F)
            (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) :=
    htc.eventually_const_lt (by simpa using hmargin)
  obtain ⟨Q, hQ⟩ := Filter.eventually_atTop.mp hev
  exact ⟨Q, hQ Q le_rfl⟩

/-- Direct enlarged positivity under the weak room condition from the blueprint, using the
split-support Bombieri--Vinogradov argument. -/
theorem enlarged_S_positive {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hθ' : θ < 1 / 2)
    (hLD : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hwit : ρ * (∫ x in enlargedSimplex k ε, (F x) ^ 2) < (θ / 2 - δ) * (∑ m, jEps k ε m F)) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
        0 < PrimeGaps.S₂ h (lambdaEps k N δ θ ε F) N w₀ -
            ρ * PrimeGaps.S₁ h (lambdaEps k N δ θ ε F) N w₀ := by
  obtain ⟨hθ0, hθ1⟩ := hθ
  set Ienl : ℝ := ∫ x in enlargedSimplex k ε, (F x) ^ 2 with hIenldef
  obtain ⟨q, hqmargin⟩ := exists_fixedWidth_Jsum_margin hk ε hε hε1 F hF hFsupp
      (θ / 2 - δ) ρ Ienl (by simpa [Ienl] using hwit)
  set η : ℝ := (((q + 1 : ℕ) : ℝ))⁻¹ with hηdef
  have hη : 0 < η := by
    rw [hηdef]
    positivity
  set Jsum : ℝ := ∑ m : Fin k, (1 + ε) ^ (k + 1) *
      PrimeGaps.J m (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
        (Grescale_contDiff hF)
        (support_rescale_subset hε hFsupp)) with hJsumdef
  obtain ⟨C1, hC1, N1, HS1⟩ := prop_s1 hk h hadm ε hε F hF hFsupp θ δ ⟨hθ0, hθ1⟩ hδ hεθ
  have hS2 : ∀ m : Fin k, ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ (N : ℝ) →
      ∀ w₀ : ZMod (W N), (∀ i, ((w₀.val : ℤ) + h i).gcd (W N) = 1) →
      PrimeGaps.S₂m h (lambdaEps k N δ θ ε F) N w₀ m ≥
        PrimeGaps.profileSecondMomentMainTerm N (R ^ (1 + ε)) (W N) m
            (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
              (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) -
          C * PrimeGaps.profileSecondMomentErrorScale N R (W N)
            (MaynardSmoothY.Fmax (Grescale ε F))
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) :=
    fun m ↦ prop_s2_fixedWidth hk h hadm m ε η hε hη F hF hFsupp
      θ δ ⟨hθ0, hθ1⟩ hθ' hLD hδ hεθ
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  choose C2 hC2 N2 HS2 using hS2
  have h1ε : (0 : ℝ) < 1 + ε := by linarith
  set Fm : ℝ := MaynardSmoothY.Fmax (Grescale ε F) with hFmdef
  set c : ℝ := (θ / 2 - δ) * Jsum - ρ * Ienl with hcdef
  have hc : 0 < c := by
    rw [hcdef]
    simpa [Jsum, η, Ienl] using hqmargin
  set E2 : ℝ := ∑ m : Fin k, C2 m *
      (Fm ^ 2 + MaynardSmoothY.Fmax (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ^ 2)
      with hE2def
  set e : ℕ → ℝ := fun N ↦ (E2 + ρ * C1 * Fm ^ 2) / PrimeGaps.D₀ (N : ℝ) with hedef
  have heT : Filter.Tendsto e Filter.atTop (𝓝 0) := by
    rw [hedef]
    exact PrimeGaps.MainProp.tendsto_coeff_div_D0 _
  have hev : ∀ᶠ N : ℕ in Filter.atTop, e N < c := heT.eventually_lt_const hc
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp hev
  set N2sup : ℝ := Finset.univ.sup' Finset.univ_nonempty N2 with hN2supdef
  refine ⟨max (max N1 N2sup) (max (rexp (rexp (rexp 2))) (max (M : ℝ) 1)), ?_⟩
  intro N hN w₀ hw₀
  obtain ⟨hNleft, hNright⟩ := max_le_iff.mp hN
  obtain ⟨hN1', hN2'⟩ := max_le_iff.mp hNleft
  obtain ⟨hNexp, hNMr⟩ := max_le_iff.mp hNright
  obtain ⟨hNM, hN1R⟩ := max_le_iff.mp hNMr
  have hN1 : 1 ≤ N := by exact_mod_cast hN1R
  have hNexp1 : (1 : ℝ) < rexp (rexp (rexp 2)) := by
    have hle := Real.add_one_le_exp (rexp (rexp 2))
    have := Real.exp_pos (rexp 2); linarith
  have hNgt1 : (1 : ℝ) < (N : ℝ) := lt_of_lt_of_le hNexp1 hNexp
  have hNposR : (0 : ℝ) < (N : ℝ) := lt_trans one_pos hNgt1
  have hWpos : (0 : ℝ) < (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos
  have hφWpos : (0 : ℝ) < ((W N).totient : ℝ) := PrimeGaps.totient_W_pos
  have hlogNpos : (0 : ℝ) < Real.log N := Real.log_pos hNgt1
  have hlogNne : Real.log (N : ℝ) ≠ 0 := ne_of_gt hlogNpos
  have hD2 : (2 : ℝ) ≤ PrimeGaps.D₀ (N : ℝ) := PrimeGaps.MaynardOffDiagonal.two_le_D0_of_large hNexp
  have hD0pos : (0 : ℝ) < PrimeGaps.D₀ (N : ℝ) := by linarith
  have hlogR : Real.log R = (θ / 2 - δ) * Real.log N := Real.log_rpow hNposR _
  have hlogRpos : 0 < Real.log R := by
    rw [hlogR]
    exact mul_pos (by linarith [hδ.2]) hlogNpos
  set sc : ℝ := PrimeGaps.mainScale k N R (W N) with hscdef
  have hscpos : 0 < sc := by rw [hscdef, PrimeGaps.mainScale]; positivity
  have hV0 : GPYSieveS1.V0Valid h (W N) w₀.val :=
    ⟨ZMod.val_lt w₀, fun i ↦ Int.isCoprime_iff_gcd_eq_one.mpr (hw₀ i)⟩
  have hHS1 := HS1 N hN1' w₀.val hV0
  have herrbase (m : Fin k) : PrimeGaps.profileSecondMomentErrorScale N R (W N) Fm
        (PrimeGaps.retainedProfile ε η m (Grescale ε F)) =
        (Fm ^ 2 + MaynardSmoothY.Fmax (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ^ 2) *
          sc / PrimeGaps.D₀ (N : ℝ) := by
    rw [hscdef, PrimeGaps.mainScale, PrimeGaps.profileSecondMomentErrorScale]
    field_simp
  have hsumMain : (∑ m, PrimeGaps.profileSecondMomentMainTerm N (R ^ (1 + ε)) (W N) m
        (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
          (Grescale_contDiff hF) (support_rescale_subset hε hFsupp))) =
          sc * (θ / 2 - δ) * Jsum := by
    have h1 : (∑ m, PrimeGaps.profileSecondMomentMainTerm N (R ^ (1 + ε)) (W N) m
          (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
            (Grescale_contDiff hF) (support_rescale_subset hε hFsupp))) =
        (((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log (R ^ (1 + ε)) ^ (k + 1) /
            ((W N : ℝ) ^ (k + 1) * Real.log N)) *
          ∑ m, PrimeGaps.J m (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
            (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl
        (fun m _ ↦ by rw [PrimeGaps.profileSecondMomentMainTerm])
    have hJsumfactor : Jsum = (1 + ε) ^ (k + 1) *
        ∑ m, PrimeGaps.J m (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m
          (Grescale ε F) (Grescale_contDiff hF)
          (support_rescale_subset hε hFsupp)) := by
      rw [hJsumdef, Finset.mul_sum]
    rw [h1, Real.log_rpow (by positivity), mul_pow, hJsumfactor, hscdef, PrimeGaps.mainScale, hlogR]
    field_simp
    ring
  have hS2ge : sc * (θ / 2 - δ) * Jsum - E2 * sc / PrimeGaps.D₀ (N : ℝ) ≤
      PrimeGaps.S₂ h (lambdaEps k N δ θ ε F) N w₀ := by
    rw [← PrimeGaps.sum_S₂m_eq_S₂]
    have hle : ∀ m ∈ (Finset.univ : Finset (Fin k)),
        PrimeGaps.profileSecondMomentMainTerm N (R ^ (1 + ε)) (W N) m
            (PrimeGaps.retainedProfileLp (ε := ε) (η := η) m (Grescale ε F)
              (Grescale_contDiff hF) (support_rescale_subset hε hFsupp)) -
          C2 m * PrimeGaps.profileSecondMomentErrorScale N R (W N)
            (MaynardSmoothY.Fmax (Grescale ε F))
            (PrimeGaps.retainedProfile ε η m (Grescale ε F)) ≤
          PrimeGaps.S₂m h (lambdaEps k N δ θ ε F) N w₀ m := by
      exact fun m _ ↦ HS2 m N (le_trans (Finset.le_sup' N2 (Finset.mem_univ m)) hN2') w₀ hw₀
    refine le_trans (le_of_eq ?_) (Finset.sum_le_sum hle)
    rw [Finset.sum_sub_distrib, hsumMain, ← hFmdef]
    simp_rw [herrbase]
    rw [hE2def, Finset.sum_mul, Finset.sum_div]
    apply congrArg (fun x ↦ sc * (θ / 2 - δ) * Jsum - x)
    apply Finset.sum_congr rfl
    intro m _
    ring
  have hS1up : PrimeGaps.S₁ h (lambdaEps k N δ θ ε F) N w₀ ≤
      sc * Ienl + C1 * Fm ^ 2 * sc / PrimeGaps.D₀ (N : ℝ) := by
    rw [PrimeGaps.MainProp.S1_eq_gpy h (lambdaEps k N δ θ ε F) N w₀]
    have hgpy : GPYSieveS1.S1 h (lambdaEps k N δ θ ε F) (N : ℝ) (W N) w₀.val ≤
        sc * Ienl + C1 * Fm ^ 2 * sc / PrimeGaps.D₀ (N : ℝ) := by
      have h2 := (abs_le.mp hHS1).2
      have hmain_eq : ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k /
          (W N : ℝ) ^ (k + 1) * Ienl = sc * Ienl := by
        rw [hscdef, PrimeGaps.mainScale]
      have herr_eq : C1 * Fm ^ 2 * ((W N).totient : ℝ) ^ k * (N : ℝ) * Real.log R ^ k /
          ((W N : ℝ) ^ (k + 1) * PrimeGaps.D₀ (N : ℝ)) =
          C1 * Fm ^ 2 * sc / PrimeGaps.D₀ (N : ℝ) := by
        rw [hscdef, PrimeGaps.mainScale]
        ring
      linarith [h2, hmain_eq, herr_eq]
    exact hgpy
  have hkey : sc * (c - e N) ≤ PrimeGaps.S₂ h (lambdaEps k N δ θ ε F) N w₀ -
        ρ * PrimeGaps.S₁ h (lambdaEps k N δ θ ε F) N w₀ := by
    have hexp : sc * (c - e N) = (sc * (θ / 2 - δ) * Jsum - E2 * sc / PrimeGaps.D₀ (N : ℝ)) -
          ρ * (sc * Ienl + C1 * Fm ^ 2 * sc / PrimeGaps.D₀ (N : ℝ)) := by
      rw [hcdef, hedef]; field_simp; ring
    rw [hexp]
    have hρ' := mul_le_mul_of_nonneg_left hS1up hρ.le
    linarith [hS2ge, hρ']
  have heN : e N < c := hM N (by exact_mod_cast hNM)
  have hpos : 0 < sc * (c - e N) := mul_pos hscpos (by linarith)
  linarith [hkey, hpos]

/-- **`prop_witness`** (witness form).  For an admissible `k`-tuple `h`,
a smooth witness `F` supported on the enlarged simplex `𝒯_ε` clearing the enlarged threshold
(the witness inequality `ρ·∫_{𝒯_ε}F² < (θ/2−δ)·∑ₘ Jᵐ_ε(F)` for some `ρ ≥ 1`), there are
infinitely many `n` with at least `2` of the shifts `n + hᵢ` simultaneously prime.

The proof is the endgame wiring: `enlarged_S_positive` gives `S₂(λ_ε) − ρ S₁(λ_ε) > 0`
eventually; compatible residues come from admissibility; `PrimeGaps.maynardTao_endgame` turns
positivity into infinitely many `n` with `⌊ρ+1⌋ ≥ 2` primes; downgrading gives `DHL[k, 2]`. -/
theorem prop_witness {k : ℕ} (hk : 2 ≤ k) (h : Fin k → ℕ) (hadm : IsAdmissible h)
    (ε : ℝ) (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hFsupp : Function.support F ⊆ enlargedSimplex k ε)
    (θ δ : ℝ) (hθ : θ ∈ Set.Ioo (0 : ℝ) 1) (hθ' : θ < 1 / 2)
    (hLD : Nat.HasLevelOfDistribution Set.univ θ 1)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2))
    (hεθ : 1 + ε < 1 / θ)
    (ρ : ℝ) (hρ1 : 1 ≤ ρ)
    (hwit : ρ * (∫ x in enlargedSimplex k ε, (F x) ^ 2) < (θ / 2 - δ) * (∑ m, jEps k ε m F)) :
    {n : ℕ | 2 ≤ #{i : Fin k | (n + h i).Prime}}.Infinite := by
  classical
  have hρ : 0 < ρ := lt_of_lt_of_le one_pos hρ1
  haveI : Nonempty (Fin k) := ⟨⟨0, by omega⟩⟩
  have hadmF : Finset.Admissible (Finset.image h Finset.univ) := hadm.2
  choose v₀ hvalid using hadmF.exists_zmod_gcd_eq_one
  obtain ⟨N₀, HS⟩ := enlarged_S_positive hk h hadm ε hε hε1 F hF hFsupp θ δ hθ hθ' hLD hδ hεθ
      ρ hρ hwit
  set Θ : ℝ := auxTheta δ θ ε
  set Δ : ℝ := auxDelta δ θ ε
  have hpos : ∀ᶠ N in atTop, ∃ l : (Fin k → ℕ) →₀ ℝ,
      0 < PrimeGaps.S₂ h l N (v₀ N) - ρ * PrimeGaps.S₁ h l N (v₀ N) := by
    rw [Filter.eventually_atTop]
    refine ⟨max ⌈N₀⌉₊ 1, fun N hN ↦ ?_⟩
    have hN1 : (1 : ℕ) ≤ N := le_trans (le_max_right _ _) hN
    have hN0 : N₀ ≤ (N : ℝ) :=
      le_trans (Nat.le_ceil N₀) (by exact_mod_cast le_trans (le_max_left _ _) hN)
    refine ⟨PrimeGaps.l₀ (PrimeGaps.sieveTruncation N Δ Θ)
      (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)), ?_⟩
    rw [show (⇑(PrimeGaps.l₀ (PrimeGaps.sieveTruncation N Δ Θ)
      (W N) (fun x ↦ Grescale ε F (WithLp.toLp 2 x)))) =
        lambdaEps k N δ θ ε F from (lambdaEps_eq_l₀_aux F hN1 hε).symm]
    exact HS N hN0 (v₀ N) (hvalid N)
  have hInf := PrimeGaps.maynardTao_endgame h ρ v₀ hpos
  have hfloor2 : (2 : ℤ) ≤ ⌊ρ + 1⌋ := by
    rw [Int.le_floor]; push_cast; linarith
  have hset : {n : ℕ | ⌊ρ + 1⌋ ≤ (#{i : Fin k | (n + h i).Prime} : ℤ)}
      ⊆ {n : ℕ | 2 ≤ #{i : Fin k | (n + h i).Prime}} := by
    intro n hn
    simp only [Set.mem_ofPred_eq] at hn ⊢
    have : (2 : ℤ) ≤ (#{i : Fin k | (n + h i).Prime} : ℤ) := le_trans hfloor2 hn
    exact_mod_cast this
  exact hInf.mono hset

end Gaps246
