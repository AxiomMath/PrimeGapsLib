/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SieveDatumEval.PartialSummation

/-!
# The layer function and the expansion of `sieveE`

Defines `sieveE` and the layer function `layerG`, and expands `sieveE` over its layers.

## Main definitions

* `sieveE`: the density-agnostic analogue of `S1E`, interpolating between the main integral
  term (`m = 0`) and the target discrete sum (`m = n`).
* `layerG`: the layer function, the cube integral of `F²` with the first `m` coordinates
  pinned by a prefix `u` and coordinate `m` pinned to a free parameter `s`.

## Main results

* `sieveE_layer_identity`
-/

@[expose] public section

open scoped Topology

open MeasureTheory

namespace PrimeGaps

/-- A function supported in the simplex `𝓡 k` vanishes at every point outside `𝓡 k`. -/
private theorem eq_zero_of_notMem_R {k : ℕ} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hsupp : Function.support F ⊆ 𝓡 k) {x : EuclideanSpace ℝ (Fin k)} (hx : x ∉ 𝓡 k) :
    F x = 0 :=
  Function.notMem_support.mp fun hmem ↦ hx (hsupp hmem)

/-- A point whose coordinates sum to more than `1` lies outside the simplex `𝓡 k`. -/
private theorem notMem_R_of_one_lt_sum {k : ℕ} {p : Fin k → ℝ} (hp : 1 < ∑ i, p i) :
    WithLp.toLp 2 p ∉ 𝓡 k := fun hmem ↦
  absurd (EuclideanSpace.mem_scaledStdSimplex_iff.mp hmem).2 (not_le.mpr hp)

/-- On the unit cube the slice indicator is redundant for an `F` supported in `𝓡 k`: where the
substituted point `g y` has coordinate sum `> 1` it lies outside `𝓡 k`, so `F` vanishes there. -/
private theorem setIntegral_slice_indicator {k : ℕ} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hsupp : Function.support F ⊆ 𝓡 k) (g : (Fin k → ℝ) → Fin k → ℝ) :
    (∫ x in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), Set.indicator
          {y : Fin k → ℝ | ∑ i, g y i ≤ 1} (fun y ↦ (F (WithLp.toLp 2 (g y))) ^ 2) x) =
      ∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1),
        (F (WithLp.toLp 2 (g y))) ^ 2 := by
  refine MeasureTheory.setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc) fun y _ ↦ ?_
  by_cases hys : y ∈ {y : Fin k → ℝ | ∑ i, g y i ≤ 1}
  · rw [Set.indicator_of_mem hys]
  · rw [Set.indicator_of_notMem hys]
    simp only [Set.mem_ofPred_eq, not_le] at hys
    rw [eq_zero_of_notMem_R hsupp (notMem_R_of_one_lt_sum hys)]
    ring

/-- For `F` supported in the simplex `𝓡 n`, `∫_{𝓡 n} F² = ∫_{[0,1]ⁿ} F²`. -/
theorem sieve_integral_cube {n : ℕ} (F : EuclideanSpace ℝ (Fin n) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 n) :
    (∫ x in 𝓡 n, (F x) ^ 2) = ∫ x in Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1),
          (F (WithLp.toLp 2 x)) ^ 2 := by
  set e := MeasurableEquiv.toLp 2 (Fin n → ℝ)
  set f : EuclideanSpace ℝ (Fin n) → (Fin n → ℝ) := ⇑e.symm
  have hmp : MeasurePreserving f volume volume :=
    EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)
  have hemb : MeasurableEmbedding f := e.symm.measurableEmbedding
  set cube : Set (Fin n → ℝ) := Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1) with hcube
  have hcov : ∫ x in f ⁻¹' cube, (F x) ^ 2 = ∫ y in cube, (F (WithLp.toLp 2 y)) ^ 2 :=
    hmp.setIntegral_preimage_emb hemb (fun y ↦ (F (WithLp.toLp 2 y)) ^ 2) cube
  have hAB : 𝓡 n ⊆ f ⁻¹' cube := fun x hx ↦ by
    simp only [Set.mem_preimage, hcube, Set.mem_pi, Set.mem_univ, forall_true_left]
    exact coord_mem_Icc_of_mem_R hx
  rw [← hcov, ← integral_indicator
      (EuclideanSpace.isClosed_scaledStdSimplex (k := n) (s := 1)).measurableSet,
    ← integral_indicator (hemb.measurable (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc))]
  congr 1
  funext x
  by_cases hxA : x ∈ 𝓡 n
  · rw [Set.indicator_of_mem hxA, Set.indicator_of_mem (hAB hxA)]
  · rw [Set.indicator_of_notMem hxA]
    by_cases hxB : x ∈ f ⁻¹' cube
    · rw [Set.indicator_of_mem hxB, eq_zero_of_notMem_R hsupp hxA]
      ring
    · rw [Set.indicator_of_notMem hxB]

/-- Density-agnostic analogue of `S1E`: for `0 ≤ m ≤ n`, the first `m` coordinates are summed
against the `SieveDatum` weight `∏ S.h (uᵢ)` (over `uᵢ ≥ 1`), the shared factor is
`(𝔖 S.γ · log z)^{n-m}`, and the remaining coordinates integrate `F²` over the truncated simplex.
`sieveE S z F 0` is the main integral term and `sieveE S z F n` is the target discrete sum.
-/
noncomputable def sieveE {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (m : ℕ) : ℝ :=
  ∑' u : Fin m → ℕ, (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) *
    ((PrimeGaps.singularSeries S.γ) * Real.log z) ^ (n - m) *
    (∫ x in Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1), Set.indicator
            {y : Fin n → ℝ |
              ∑ i : Fin n, (if h : (i : ℕ) < m then
                      Real.log (u ⟨i, h⟩) / Real.log z
                    else y i) ≤ 1}
            (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
                    Real.log (u ⟨i, h⟩) / Real.log z
                  else y i))) ^ 2) x)

/-- `sieveE S z F 0 = (𝔖 S.γ · log z)^n · ∫_{𝓡 n} F²` (via `sieve_integral_cube`). -/
theorem sieveE_zero {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : Function.support F ⊆ 𝓡 n) :
    sieveE S z F 0 =
      ((PrimeGaps.singularSeries S.γ) * Real.log z) ^ n * (∫ x in 𝓡 n, (F x) ^ 2) := by
  unfold sieveE
  rw [tsum_eq_single (default : Fin 0 → ℕ) (fun b hb ↦ absurd (Subsingleton.elim b default) hb),
    if_pos (fun i ↦ i.elim0 : ∀ i, 1 ≤ (default : Fin 0 → ℕ) i),
    Finset.prod_eq_one (fun i _ ↦ i.elim0), Nat.sub_zero,
    sieve_integral_cube F hsupp, one_mul]
  congr 1
  rw [setIntegral_slice_indicator hsupp fun y i ↦ if h : (i : ℕ) < 0 then
    Real.log ((default : Fin 0 → ℕ) ⟨i, h⟩) / Real.log z else y i]
  refine MeasureTheory.setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc) fun y _ ↦ ?_
  rw [show (fun i : Fin n ↦ if h : (i : ℕ) < 0 then
      Real.log ((default : Fin 0 → ℕ) ⟨i, h⟩) / Real.log z else y i) = y from
    funext fun i ↦ dif_neg (Nat.not_lt_zero _)]

section LayerGCore
variable {k : ℕ}

/-- A continuous real function that vanishes on the open ray `{x + t • v : t > 0}` also vanishes
at the endpoint `x`. -/
private theorem eq_zero_of_forall_pos_smul_add {k : ℕ} {F : EuclideanSpace ℝ (Fin k) → ℝ}
    (hFcont : Continuous F) (x v : EuclideanSpace ℝ (Fin k))
    (hray : ∀ t : ℝ, 0 < t → F (x + t • v) = 0) : F x = 0 := by
  have hcont : Continuous fun t : ℝ ↦ F (x + t • v) := by fun_prop
  have htend : Filter.Tendsto (fun t : ℝ ↦ F (x + t • v)) (𝓝[Set.Ioi 0] 0) (𝓝 (F x)) :=
    Filter.Tendsto.mono_left (by simpa only [zero_smul, add_zero] using hcont.tendsto 0)
      nhdsWithin_le_nhds
  refine tendsto_nhds_unique htend (Filter.Tendsto.congr' ?_ tendsto_const_nhds)
  filter_upwards [self_mem_nhdsWithin] with t ht using (hray t ht).symm

/-- A continuous `F` supported on the closed simplex `𝓡 k` vanishes at every boundary point of
`𝓡 k` (a face where some coordinate is `0`, or where the coordinate sum equals `1`).
-/
theorem S1_boundary_vanish {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k)
    {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ 𝓡 k)
    (hbdry : (∃ i, x.ofLp i = 0) ∨ (∑ i, x.ofLp i = 1)) : F x = 0 := by
  have hFcont : Continuous F := hF.continuous
  have hFzero : ∀ y, y ∉ 𝓡 k → F y = 0 := fun _ ↦ eq_zero_of_notMem_R hsupp
  rcases hbdry with ⟨j, hj⟩ | hsum
  · set v : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single j (-1 : ℝ) with hv
    refine eq_zero_of_forall_pos_smul_add hFcont x v fun t ht ↦ hFzero _ ?_
    rw [EuclideanSpace.mem_scaledStdSimplex_iff]
    push Not
    intro hnn
    have hj' := hnn j
    rw [show (x + t • v).ofLp j = -t by
      simp only [WithLp.ofLp_add, WithLp.ofLp_smul, hv, PiLp.ofLp_single, Pi.add_apply,
        Pi.smul_apply, smul_eq_mul, Pi.single_eq_same]
      rw [hj]
      ring] at hj'
    linarith
  · obtain ⟨j⟩ : Nonempty (Fin k) := Fin.pos_iff_nonempty.mp <| Nat.pos_of_ne_zero <| by
      rintro rfl
      simp at hsum
    set v : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single j (1 : ℝ) with hv
    refine eq_zero_of_forall_pos_smul_add hFcont x v fun t ht ↦ hFzero _ ?_
    rw [EuclideanSpace.mem_scaledStdSimplex_iff]
    push Not
    intro _
    have hpt : ∀ i : Fin k, (x + t • v).ofLp i = x.ofLp i + t * v.ofLp i := fun i ↦ rfl
    have hvsum : ∑ i, v.ofLp i = 1 := by simp [hv]
    rw [show ∑ i, (x + t • v).ofLp i = 1 + t by
      simp only [hpt, Finset.sum_add_distrib, ← Finset.mul_sum, hvsum, hsum, mul_one]]
    linarith

/-- For a prefix `u: Fin m → ℕ`, `layerG z F u s` is the set-integral over the ambient cube
`[0,1]^k` of `F²` of the substituted point where coordinates `i < m` are fixed to `log(uᵢ)/log R`,
coordinate `m` is fixed to the free value `s`, and coordinates `i > m` are the integration
variables `y i`, restricted by `∑ (substituted) ≤ 1`.
-/
noncomputable def layerG (z : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    {m : ℕ} (u : Fin m → ℕ) (s : ℝ) : ℝ :=
  ∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), Set.indicator
      {y : Fin k → ℝ |
        ∑ i : Fin k, (if h : (i : ℕ) < m then
                Real.log (u ⟨i, h⟩) / Real.log z
              else if (i : ℕ) = m then s else y i) ≤ 1}
      (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
              Real.log (u ⟨i, h⟩) / Real.log z
            else if (i : ℕ) = m then s else y i))) ^ 2) y

/-- (first conjunct of L1). The integrand is `≤ Fmax²` pointwise on the cube (volume `1`), so the
set-integral is `≤ Fmax²`. Direct adaptation of `S1_peeledG_bounded`.
-/
theorem S1_layerG_bounded {m : ℕ} (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, |layerG z F u s| ≤ (MaynardSmoothY.Fmax F) ^ 2 := by
  intro s hs
  set cube : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1) with hcube
  set slice : Set (Fin k → ℝ) :=
    {y : Fin k → ℝ |
        ∑ i : Fin k, (if h : (i : ℕ) < m then
                Real.log (u ⟨i, h⟩) / Real.log z
              else if (i : ℕ) = m then s else y i) ≤ 1}
  set g : (Fin k → ℝ) → ℝ := fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
              Real.log (u ⟨i, h⟩) / Real.log z
            else if (i : ℕ) = m then s else y i))) ^ 2
  have hfin : MeasureTheory.volume cube < ⊤ := by
    rw [hcube]
    exact (isCompact_univ_pi fun _ ↦ isCompact_Icc).measure_lt_top
  have hbound : ∀ y ∈ cube, ‖(Set.indicator slice g) y‖ ≤ (MaynardSmoothY.Fmax F) ^ 2 := by
    intro y _
    by_cases hys : y ∈ slice
    · rw [Set.indicator_of_mem hys]
      set p : Fin k → ℝ := fun i ↦ if h : (i : ℕ) < m then
              Real.log (u ⟨i, h⟩) / Real.log z
            else if (i : ℕ) = m then s else y i
      rw [show g y = (F (WithLp.toLp 2 p)) ^ 2 from rfl, Real.norm_eq_abs,
        abs_of_nonneg (sq_nonneg _)]
      by_cases hpin : ∀ i, p i ∈ Set.Icc (0 : ℝ) 1
      · obtain ⟨h1, h2⟩ :=
          abs_le.mp (MaynardSmoothY.abs_F_le_Fmax F hF (x := WithLp.toLp 2 p) hpin)
        exact sq_le_sq' h1 h2
      · push Not at hpin
        obtain ⟨i0, hi0⟩ := hpin
        rw [eq_zero_of_notMem_R hsupp fun hmem ↦ hi0 (coord_mem_Icc_of_mem_R hmem i0)]
        simpa using sq_nonneg (MaynardSmoothY.Fmax F)
    · rw [Set.indicator_of_notMem hys]
      simpa using sq_nonneg (MaynardSmoothY.Fmax F)
  have hkey := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hbound
  have hvol : MeasureTheory.volume.real cube = 1 := by
    rw [MeasureTheory.measureReal_def, hcube, MeasureTheory.volume_pi_pi]
    simp [Real.volume_Icc]
  rw [hvol, mul_one] at hkey
  rw [show layerG z F u s = ∫ y in cube, (Set.indicator slice g) y from rfl]
  simpa [Real.norm_eq_abs] using hkey

/-- For any point `x`, `|F x| ≤ Fmax F`: if `x ∈ 𝓡 k` then all its coords lie in `[0,1]` and
`MaynardSmoothY.abs_F_le_Fmax` applies; otherwise `F x = 0 ≤ Fmax F`.
-/
theorem S1_abs_F_le_Fmax_global {k : ℕ} (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hsupp : Function.support F ⊆ 𝓡 k)
    (x : EuclideanSpace ℝ (Fin k)) : |F x| ≤ MaynardSmoothY.Fmax F := by
  by_cases hx : x ∈ 𝓡 k
  · exact MaynardSmoothY.abs_F_le_Fmax F hF (coord_mem_Icc_of_mem_R hx)
  · rw [eq_zero_of_notMem_R hsupp hx, abs_zero]
    exact MaynardSmoothY.Fmax_nonneg F hF

/-- Outside the slice (`∑ subst > 1`), the substituted point has coordinate sum `> 1`, hence is
`∉ 𝓡 k`, so `F` there is `0`; thus the slice indicator is redundant and
`layerG s = ∫_cube F(subst s y)²`.
-/
theorem S1_layerG_eq_integral {m : ℕ} (z : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) (s : ℝ) :
    layerG z F u s = ∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), (F (WithLp.toLp 2
            (fun i ↦ if h : (i : ℕ) < m then
                Real.log (u ⟨i, h⟩) / Real.log z
              else if (i : ℕ) = m then s else y i))) ^ 2 := by
  unfold layerG
  exact setIntegral_slice_indicator hsupp fun y i ↦ if h : (i : ℕ) < m then
    Real.log (u ⟨i, h⟩) / Real.log z else if (i : ℕ) = m then s else y i

/-- Continuity in the free coordinates `y` of the layer integrand `y ↦ F x ^ 2`, where `x` freezes
the first `m` coordinates at `log (u i) / log z` and coordinate `m` at `s`. -/
theorem S1_layerG_integrand_cont {m : ℕ} (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (u : Fin m → ℕ) (s : ℝ) :
    Continuous (fun y : Fin k → ℝ ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
            Real.log (u ⟨i, h⟩) / Real.log z
          else if (i : ℕ) = m then s else y i))) ^ 2) := by
  refine Continuous.pow (hF.continuous.comp ((PiLp.continuous_toLp 2 _).comp
    (continuous_pi fun i ↦ ?_))) 2
  split_ifs <;> first | exact continuous_const | exact continuous_apply i

/-- Since the substituted points at `s` and `t` differ only in coordinate `m` (set to `s` resp.
`t`), and `|∂_m F| ≤ Fmax`, `|F(subst s y)² − F(subst t y)²| ≤ 2·Fmax²·|s − t|`. Uses the global
bound `S1_abs_F_le_Fmax_global` on `|F(A)+F(B)|` and a one-variable mean-value estimate for
`|F(A) − F(B)|`.
-/
theorem S1_F_sq_coord_bound {m : ℕ} (hm : m < k) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) (s t : ℝ)
    (y : Fin k → ℝ) :
    |(F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
              Real.log (u ⟨i, h⟩) / Real.log z
            else if (i : ℕ) = m then s else y i))) ^ 2 - (F (WithLp.toLp 2
          (fun i ↦ if h : (i : ℕ) < m then
              Real.log (u ⟨i, h⟩) / Real.log z
            else if (i : ℕ) = m then t else y i))) ^ 2| ≤
      2 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t| := by
  set m' : Fin k := ⟨m, hm⟩ with hm'
  set subst : ℝ → (Fin k → ℝ) := fun r i ↦ if h : (i : ℕ) < m then Real.log (u ⟨i, h⟩) / Real.log z
    else if (i : ℕ) = m then r else y i with hsubst
  set G : ℝ → ℝ := fun r ↦ F (WithLp.toLp 2 (subst r)) with hG
  set em : EuclideanSpace ℝ (Fin k) := EuclideanSpace.single m' (1 : ℝ) with hem
  set base : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (subst 0) with hbase
  have hPeq : ∀ r : ℝ, WithLp.toLp 2 (subst r) = base + r • em := by
    intro r
    rw [hbase, hem]
    ext i
    simp only [WithLp.ofLp_add, WithLp.ofLp_smul, PiLp.ofLp_single,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul, hsubst]
    rw [Pi.single_apply]
    by_cases h1 : (i : ℕ) < m
    · rw [dif_pos h1, dif_pos h1,
        if_neg (by intro hc; rw [hc] at h1; simp only [hm'] at h1; exact absurd h1 (lt_irrefl _))]
      ring
    · rw [dif_neg h1, dif_neg h1]
      by_cases h2 : (i : ℕ) = m
      · rw [if_pos h2, if_pos h2, if_pos (Fin.ext (by simpa [hm'] using h2))]
        ring
      · rw [if_neg h2, if_neg h2, if_neg (by intro hc; exact h2 (by simp [hm', hc]))]
        ring
  have hGeq : G = fun r : ℝ ↦ F (base + r • em) := funext fun r ↦ congrArg F (hPeq r)
  have hFmax_nonneg : 0 ≤ MaynardSmoothY.Fmax F := MaynardSmoothY.Fmax_nonneg F hF
  have hGderiv : ∀ r : ℝ, HasDerivAt G (fderiv ℝ F (base + r • em) em) r := fun r ↦ by
    rw [hGeq]
    refine ((hF.differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt r ?_
    simpa using ((hasDerivAt_id r).smul_const em).const_add base
  have hderiv_bound : ∀ r : ℝ, ‖deriv G r‖ ≤ MaynardSmoothY.Fmax F := by
    intro r
    rw [(hGderiv r).deriv, Real.norm_eq_abs]
    set Pr : EuclideanSpace ℝ (Fin k) := base + r • em
    by_cases hin : Pr ∈ 𝓡 k
    · have hle : |F Pr| + ∑ i, |(fderiv ℝ F Pr) (EuclideanSpace.single i 1)| ≤
          MaynardSmoothY.Fmax F :=
        le_csSup (MaynardSmoothY.abs_F_bddAbove F hF) ⟨Pr, coord_mem_Icc_of_mem_R hin, rfl⟩
      have hsingle : |(fderiv ℝ F Pr) (EuclideanSpace.single m' 1)| ≤
          ∑ i, |(fderiv ℝ F Pr) (EuclideanSpace.single i 1)| :=
        Finset.single_le_sum (f := fun i ↦ |(fderiv ℝ F Pr) (EuclideanSpace.single i 1)|)
          (fun i _ ↦ abs_nonneg _) (Finset.mem_univ m')
      rw [hem]
      linarith [abs_nonneg (F Pr)]
    · have hev : F =ᶠ[𝓝 Pr] (fun _ ↦ 0) := by
        filter_upwards [(EuclideanSpace.isClosed_scaledStdSimplex
          (k := k) (s := 1)).isOpen_compl.mem_nhds hin] with w hw using
          eq_zero_of_notMem_R hsupp hw
      rw [(hasFDerivAt_zero_of_eventually_const 0 hev).fderiv]
      simp [hFmax_nonneg]
  have hlip : ‖G s - G t‖ ≤ MaynardSmoothY.Fmax F * ‖s - t‖ :=
    Convex.norm_image_sub_le_of_norm_deriv_le
      (fun r _ ↦ (hGderiv r).differentiableAt) (fun r _ ↦ hderiv_bound r) convex_univ
      (Set.mem_univ t) (Set.mem_univ s)
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at hlip
  have hGs_bd : |G s| ≤ MaynardSmoothY.Fmax F := S1_abs_F_le_Fmax_global F hF hsupp _
  have hGt_bd : |G t| ≤ MaynardSmoothY.Fmax F := S1_abs_F_le_Fmax_global F hF hsupp _
  change |G s ^ 2 - G t ^ 2| ≤ 2 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t|
  rw [show G s ^ 2 - G t ^ 2 = (G s - G t) * (G s + G t) by ring, abs_mul]
  calc |G s - G t| * |G s + G t|
      ≤ (MaynardSmoothY.Fmax F * |s - t|) * (2 * MaynardSmoothY.Fmax F) :=
        mul_le_mul hlip ((abs_add_le _ _).trans (by linarith)) (abs_nonneg _)
          (mul_nonneg hFmax_nonneg (abs_nonneg _))
    _ = 2 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t| := by ring

/-- (second conjunct of L1). -/
theorem S1_layerG_lipschitz {m : ℕ} (hm : m < k) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) :
    ∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |layerG z F u s - layerG z F u t| ≤ 3 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t| := by
  intro s hs t ht
  rw [S1_layerG_eq_integral z F hsupp u s, S1_layerG_eq_integral z F hsupp u t]
  set cube : Set (Fin k → ℝ) := Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1) with hcube
  set gs : (Fin k → ℝ) → ℝ := fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
          Real.log (u ⟨i, h⟩) / Real.log z
        else if (i : ℕ) = m then s else y i))) ^ 2 with hgs
  set gt : (Fin k → ℝ) → ℝ := fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
          Real.log (u ⟨i, h⟩) / Real.log z
        else if (i : ℕ) = m then t else y i))) ^ 2 with hgt
  have hcpt : IsCompact cube := by
    rw [hcube]
    exact isCompact_univ_pi fun _ ↦ isCompact_Icc
  have hvol : MeasureTheory.volume.real cube = 1 := by
    rw [MeasureTheory.measureReal_def, hcube, MeasureTheory.volume_pi_pi]
    simp [Real.volume_Icc]
  rw [← MeasureTheory.integral_sub
    ((S1_layerG_integrand_cont z F hF u s).continuousOn.integrableOn_compact hcpt)
    ((S1_layerG_integrand_cont z F hF u t).continuousOn.integrableOn_compact hcpt)]
  have hbound : ∀ y ∈ cube, ‖gs y - gt y‖ ≤ 2 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t| := by
    intro y _
    rw [Real.norm_eq_abs, hgs, hgt]
    exact S1_F_sq_coord_bound hm z F hF hsupp u s t y
  have hfin : MeasureTheory.volume cube < ⊤ := hcpt.measure_lt_top
  have hkey := MeasureTheory.norm_setIntegral_le_of_norm_le_const hfin hbound
  rw [hvol, mul_one, Real.norm_eq_abs] at hkey
  calc |∫ y in cube, (gs y - gt y)| ≤ 2 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t| := hkey
    _ ≤ 3 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t| := by
        nlinarith [sq_nonneg (MaynardSmoothY.Fmax F), abs_nonneg (s - t)]

/-- The correct peeled function is bounded by `Fmax²` (integrand `≤ Fmax²`, cube volume `= 1`) and
`3·Fmax²` -Lipschitz on `[0,1]` (common-region `∂ₛF²` bound `≤ 2Fmax²` plus the moving-face
symmetric-difference slice of volume `≤ |s-t|`, using `S1_boundary_vanish` for continuity at the
moving face).
-/
theorem S1_layerG_bdd_lip {m : ℕ} (hm : m < k) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) :
    (∀ s ∈ Set.Icc (0 : ℝ) 1, |layerG z F u s| ≤ (MaynardSmoothY.Fmax F) ^ 2) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1,
        |layerG z F u s - layerG z F u t| ≤ 3 * (MaynardSmoothY.Fmax F) ^ 2 * |s - t|) :=
  ⟨S1_layerG_bounded z F hF hsupp u, S1_layerG_lipschitz hm z F hF hsupp u⟩

/-- The substitution used inside `S1E … (m+1)` pins coordinate `i < m+1` to `log (v i)/log R`;
writing `v = Fin.snoc u d`, this is `u ⟨i⟩` for `i < m` and `d` for `i = m`, matching exactly the
substitution defining `layerG z F u (log d/log R)`. Pure `funext` congruence; no Fubini.
-/
theorem S1Em1_inner_eq_layerG {m : ℕ} (z : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) (d : ℕ) :
    (∫ x in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), Set.indicator
          {y : Fin k → ℝ |
            ∑ i : Fin k, (if h : (i : ℕ) < m + 1 then
                    Real.log ((Fin.snoc u d : Fin (m + 1) → ℕ) ⟨i, h⟩) / Real.log z
                  else y i) ≤ 1}
          (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m + 1 then
                  Real.log ((Fin.snoc u d : Fin (m + 1) → ℕ) ⟨i, h⟩) / Real.log z
                else y i))) ^ 2) x) = layerG z F u (Real.log d / Real.log z) := by
  have hsubst : ∀ (y : Fin k → ℝ), (fun i : Fin k ↦ if h : (i : ℕ) < m + 1 then
          Real.log ((Fin.snoc u d : Fin (m + 1) → ℕ) ⟨i, h⟩) / Real.log z
        else y i) = (fun i : Fin k ↦ if h : (i : ℕ) < m then
          Real.log (u ⟨i, h⟩) / Real.log z
        else if (i : ℕ) = m then
          Real.log d / Real.log z
        else y i) := by
    intro y
    funext i
    by_cases h1 : (i : ℕ) < m
    · rw [dif_pos (Nat.lt_succ_of_lt h1), dif_pos h1,
        show (⟨(i : ℕ), Nat.lt_succ_of_lt h1⟩ : Fin (m + 1)) = Fin.castSucc ⟨(i : ℕ), h1⟩ from rfl,
        Fin.snoc_castSucc]
    · by_cases h2 : (i : ℕ) = m
      · have hlt : (i : ℕ) < m + 1 := by omega
        rw [dif_pos hlt, dif_neg h1, if_pos h2,
          show (⟨(i : ℕ), hlt⟩ : Fin (m + 1)) = Fin.last m from Fin.ext (by simpa using h2),
          Fin.snoc_last]
      · rw [dif_neg (by omega : ¬ ((i : ℕ) < m + 1)), dif_neg h1, if_neg h2]
  rw [S1_layerG_eq_integral z F hsupp u (Real.log d / Real.log z),
    setIntegral_slice_indicator hsupp fun y i ↦ if h : (i : ℕ) < m + 1 then
      Real.log ((Fin.snoc u d : Fin (m + 1) → ℕ) ⟨i, h⟩) / Real.log z else y i]
  refine MeasureTheory.setIntegral_congr_fun
    (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc) fun y _ ↦ ?_
  rw [hsubst y]

/-- If some `u j` (with `j < m`) satisfies `R < (u j: ℝ)`, then the substituted point has
coordinate `j` equal to `log(u j)/log R > 1`, so it lies outside `𝓡 k` (where every coordinate is
`≤` the sum `≤ 1`), hence `F` vanishes there and the integral is `0`.
-/
theorem S1_layerG_eq_zero_of_coord_ge {m : ℕ} (hm : m < k) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) (s : ℝ)
    (hz : 2 ≤ z)
    (j : Fin m) (hj : z < (u j : ℝ)) :
    layerG z F u s = 0 := by
  rw [S1_layerG_eq_integral z F hsupp u s]
  have hR0 : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  set J : Fin k := ⟨(j : ℕ), lt_of_lt_of_le j.isLt hm.le⟩
  have hJlt : (J : ℕ) < m := j.isLt
  have hcoordgt1 : 1 < Real.log (u j) / Real.log z := by
    rw [lt_div_iff₀ hR0, one_mul]
    exact Real.log_lt_log (by linarith) hj
  refine MeasureTheory.integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  set p : Fin k → ℝ := fun i ↦ if h : (i : ℕ) < m then
      Real.log (u ⟨i, h⟩) / Real.log z
    else if (i : ℕ) = m then s else y i with hpdef
  have hpJ : p J = Real.log (u j) / Real.log z := by
    rw [hpdef]
    simp only [dif_pos hJlt]
    congr 2
  change (F (WithLp.toLp 2 p)) ^ 2 = 0
  rw [eq_zero_of_notMem_R hsupp fun hmem ↦ by
    have hJle : p J ≤ 1 := (coord_mem_Icc_of_mem_R hmem J).2
    rw [hpJ] at hJle
    linarith]
  ring

/-- The free coordinate `m` is pinned to `s ≥ 1`; on the cube all coordinates are `≥ 0`, so the
coordinate sum is `≥ s ≥ 1`. If the sum exceeds `1` the point is outside `𝓡 k` and `F` vanishes; if
it equals `1` the point is on the boundary of `𝓡 k`, where a continuous `F` supported on `𝓡 k`
vanishes (`S1_boundary_vanish`). Either way the integrand is `0`, so `layerG z F u s = 0`.
-/
theorem S1_layerG_eq_zero_of_arg_ge_one {m : ℕ} (hm : m < k) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) (s : ℝ)
    (hz : 2 ≤ z) (hs : 1 ≤ s) :
    layerG z F u s = 0 := by
  rw [S1_layerG_eq_integral z F hsupp u s]
  have hR0 : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  set M : Fin k := ⟨m, hm⟩ with hM
  refine MeasureTheory.integral_eq_zero_of_ae ?_
  rw [Filter.eventuallyEq_iff_exists_mem]
  refine ⟨Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1),
    MeasureTheory.self_mem_ae_restrict (MeasurableSet.univ_pi fun _ ↦ measurableSet_Icc), ?_⟩
  intro y hy
  simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc] at hy
  set p : Fin k → ℝ := fun i ↦ if h : (i : ℕ) < m then
      Real.log (u ⟨i, h⟩) / Real.log z
    else if (i : ℕ) = m then s else y i with hpdef
  have hpnn : ∀ i, 0 ≤ p i := by
    intro i
    rw [hpdef]
    dsimp only
    split_ifs with h1 h2
    · exact div_nonneg (Real.log_natCast_nonneg _) hR0.le
    · linarith
    · exact (hy i).1
  have hpM : p M = s := by
    rw [hpdef]
    simp only [dif_neg (by rw [hM]; simp : ¬ ((M : ℕ) < m))]
    rw [if_pos (show ((M : Fin k) : ℕ) = m from rfl)]
  have hMle : p M ≤ ∑ i, p i := Finset.single_le_sum (fun i _ ↦ hpnn i) (Finset.mem_univ M)
  change (F (WithLp.toLp 2 p)) ^ 2 = 0
  by_cases hmem : WithLp.toLp 2 p ∈ 𝓡 k
  · have hle1 : ∑ i, p i ≤ 1 := (EuclideanSpace.mem_scaledStdSimplex_iff.mp hmem).2
    have hsum1 : ∑ i, (WithLp.toLp 2 p : EuclideanSpace ℝ (Fin k)).ofLp i = 1 := by
      rw [hpM] at hMle
      exact le_antisymm hle1 (by linarith)
    rw [S1_boundary_vanish F hF hsupp hmem (Or.inr hsum1)]
    ring
  · rw [eq_zero_of_notMem_R hsupp hmem]
    ring

/-- Outside the slice `∑ subst > 1`, the substituted point lies outside `𝓡 k`, so `F` vanishes
there; the indicator is therefore redundant. (Same argument as `S1_layerG_eq_integral`.)
-/
theorem S1Em_inner_drop_indicator {m : ℕ} (z : ℝ) (F : EuclideanSpace ℝ (Fin k) → ℝ)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) :
    (∫ x in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), Set.indicator
          {y : Fin k → ℝ |
            ∑ i : Fin k, (if h : (i : ℕ) < m then
                    Real.log (u ⟨i, h⟩) / Real.log z
                  else y i) ≤ 1}
          (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
                  Real.log (u ⟨i, h⟩) / Real.log z
                else y i))) ^ 2) x) = ∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1),
          (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
                Real.log (u ⟨i, h⟩) / Real.log z
              else y i))) ^ 2 :=
  setIntegral_slice_indicator hsupp fun y i ↦ if h : (i : ℕ) < m then
    Real.log (u ⟨i, h⟩) / Real.log z else y i

/-- The `k` -dimensional unit cube. -/
private lemma S1cube_isCompact (k : ℕ) :
    IsCompact (Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1)) :=
  isCompact_univ_pi fun _ ↦ isCompact_Icc

/-- Split off coordinate `i` of a cube integral as a `∫ t in Icc, ∫ y' in cube_{k-1}` change of
variables (via the measure-preserving `piFinSuccAbove` equiv).
-/
private lemma S1cube_split {n : ℕ} (i : Fin (n + 1)) (Φ : (Fin (n + 1) → ℝ) → ℝ)
    (hΦ : Continuous Φ) :
    (∫ y in Set.pi Set.univ (fun _ : Fin (n + 1) ↦ Set.Icc (0 : ℝ) 1), Φ y) =
      ∫ t in Set.Icc (0 : ℝ) 1,
          ∫ y' in Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1), Φ (i.insertNth t y') := by
  set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i
  have hmp : MeasureTheory.MeasurePreserving e (MeasureTheory.volume) (MeasureTheory.volume) :=
    MeasureTheory.volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) i
  have hemb : MeasurableEmbedding e := e.measurableEmbedding
  have hpre : (Set.pi Set.univ (fun _ : Fin (n + 1) ↦ Set.Icc (0 : ℝ) 1)) =
      e ⁻¹' (Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)) := by
    ext f
    simp only [Set.mem_pi, Set.mem_univ, true_implies, Set.mem_preimage, Set.mem_prod]
    rw [Fin.forall_iff_succAbove i]
    rfl
  have hcov : (∫ y in Set.pi Set.univ (fun _ : Fin (n + 1) ↦ Set.Icc (0 : ℝ) 1), Φ y) =
      ∫ p in (Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1)),
          Φ (e.symm p) := by
    rw [hpre]
    simpa only [MeasurableEquiv.symm_apply_apply] using hmp.setIntegral_preimage_emb hemb
      (fun p ↦ Φ (e.symm p))
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1))
  rw [hcov, MeasureTheory.Measure.volume_eq_prod ℝ (Fin n → ℝ), MeasureTheory.setIntegral_prod]
  · exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ ↦
      MeasureTheory.setIntegral_congr_fun (S1cube_isCompact n).measurableSet fun y' _ ↦ rfl
  · refine ContinuousOn.integrableOn_compact (isCompact_Icc.prod (S1cube_isCompact n)) ?_
    exact (hΦ.comp (by fun_prop :
      Continuous fun p : ℝ × (Fin n → ℝ) ↦ i.insertNth (α := fun _ ↦ ℝ) p.1 p.2)).continuousOn

/-- `Function.update (i.insertNth t y') i s = i.insertNth s y'`. -/
private lemma S1insertNth_update {n : ℕ} (i : Fin (n + 1)) (t s : ℝ) (y' : Fin n → ℝ) :
    Function.update (i.insertNth (α := fun _ ↦ ℝ) t y') i s =
      i.insertNth (α := fun _ ↦ ℝ) s y' := by
  ext j
  rcases eq_or_ne j i with hj | hj
  · subst hj
    simp [Fin.insertNth_apply_same]
  · rw [Function.update_of_ne hj]
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    simp only [Fin.insertNth_apply_succAbove]

/-- Fubini "peel one coordinate into `s ∈ [0,1]` " for a cube integral: the free coordinate `i`
becomes the integration variable `s`, the remaining coordinates integrate over the cube (with the
now-dummy `i` -th factor of measure 1).
-/
private lemma S1cube_update_split {k : ℕ} (i : Fin k) (Φ : (Fin k → ℝ) → ℝ) (hΦ : Continuous Φ) :
    (∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), Φ y) = ∫ s in (0 : ℝ)..1,
          ∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1),
            Φ (Function.update y i s) := by
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, (Nat.succ_pred_eq_of_pos i.pos).symm⟩
  set H : ℝ → ℝ := fun s ↦
    ∫ y' in Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1), Φ (i.insertNth s y') with hH
  have hRHSinner : ∀ s : ℝ,
      (∫ y in Set.pi Set.univ (fun _ : Fin (n + 1) ↦ Set.Icc (0 : ℝ) 1),
        Φ (Function.update y i s)) = H s := by
    intro s
    rw [S1cube_split i (fun y ↦ Φ (Function.update y i s)) (hΦ.comp (by fun_prop))]
    have hstep : (∫ t in Set.Icc (0 : ℝ) 1, ∫ y' in Set.pi Set.univ (fun _ : Fin n ↦
      Set.Icc (0 : ℝ) 1), Φ (Function.update (i.insertNth (α := fun _ ↦ ℝ) t y') i s)) =
        ∫ t in Set.Icc (0 : ℝ) 1, H s := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun t _ ↦ ?_
      simp only [hH]
      exact MeasureTheory.setIntegral_congr_fun (S1cube_isCompact n).measurableSet
        fun y' _ ↦ by simp only [S1insertNth_update]
    rw [hstep, MeasureTheory.setIntegral_const,
      show (MeasureTheory.volume : MeasureTheory.Measure ℝ).real (Set.Icc (0 : ℝ) 1) = 1 by
        simp [MeasureTheory.measureReal_def, Real.volume_Icc], one_smul]
  rw [S1cube_split i Φ hΦ, intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    MeasureTheory.integral_Icc_eq_integral_Ioc]
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioc fun s _ ↦ (hRHSinner s).symm

/-- Splitting off the `m` -th cube factor as an integration variable `s ∈ [0,1]`: the free
coordinate `m` (value `y m`) is renamed `s`, and the remaining coordinates integrate over the cube
(with the now-dummy `m` -th factor of measure 1).
-/
theorem S1Em_fubini_coord {m : ℕ} (hm : m < k) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (u : Fin m → ℕ) :
    (∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), (F (WithLp.toLp 2
          (fun i ↦ if h : (i : ℕ) < m then
              Real.log (u ⟨i, h⟩) / Real.log z
            else y i))) ^ 2) = ∫ s in (0 : ℝ)..1,
          ∫ y in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), (F (WithLp.toLp 2
              (fun i ↦ if h : (i : ℕ) < m then
                  Real.log (u ⟨i, h⟩) / Real.log z
                else if (i : ℕ) = m then s else y i))) ^ 2 := by
  set idx : Fin k := ⟨m, hm⟩ with hidx
  set Φ : (Fin k → ℝ) → ℝ := fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
            Real.log (u ⟨i, h⟩) / Real.log z
          else y i))) ^ 2 with hΦdef
  have hΦcont : Continuous Φ := by
    simp only [hΦdef]
    refine Continuous.pow (hF.continuous.comp
      ((PiLp.continuous_toLp 2 (fun _ : Fin k ↦ ℝ)).comp (continuous_pi fun i ↦ ?_))) 2
    split_ifs <;> first | exact continuous_const | exact continuous_apply i
  have hkey := S1cube_update_split idx Φ hΦcont
  rw [hΦdef] at hkey
  rw [hkey]
  refine intervalIntegral.integral_congr fun s _ ↦
    MeasureTheory.setIntegral_congr_fun (S1cube_isCompact k).measurableSet fun y _ ↦ ?_
  refine congrArg (fun w : Fin k → ℝ ↦ (F (WithLp.toLp 2 w)) ^ 2) (funext fun i ↦ ?_)
  by_cases him : (i : ℕ) = m
  · rw [show i = idx by rw [hidx, Fin.ext_iff]; exact him, Function.update_self,
      if_pos (show ((idx : Fin k) : ℕ) = m from rfl)]
  · rw [Function.update_of_ne (by rw [hidx, Fin.ne_iff_vne]; simpa using him), if_neg him]

/-- The `E_m` inner integral fixes coordinates `< m` and integrates coordinates `≥ m` over the
cube; separating out coordinate `m` (Fubini) as an integration variable `s ∈ [0,1]` reconstructs
`∫₀¹ layerG u s ds` (whose `y_m` factor is a dummy of measure 1).
-/
theorem S1Em_inner_eq_layerG_int {m : ℕ} (hm : m < k) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin k) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 k) (u : Fin m → ℕ) :
    (∫ x in Set.pi Set.univ (fun _ : Fin k ↦ Set.Icc (0 : ℝ) 1), Set.indicator
          {y : Fin k → ℝ |
            ∑ i : Fin k, (if h : (i : ℕ) < m then
                    Real.log (u ⟨i, h⟩) / Real.log z
                  else y i) ≤ 1}
          (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m then
                  Real.log (u ⟨i, h⟩) / Real.log z
                else y i))) ^ 2) x) = ∫ s in (0 : ℝ)..1, layerG z F u s := by
  rw [S1Em_inner_drop_indicator z F hsupp u, S1Em_fubini_coord hm z F hF u]
  exact intervalIntegral.integral_congr fun s _ ↦ (S1_layerG_eq_integral z F hsupp u s).symm

end LayerGCore

/-- (density-agnostic). The `sieveE` weight of the length-`(m+1)` tuple `Fin.snoc u d` factors as
the length-`m` weight of `u` times the single-index weight of `d`.
-/
theorem sieveDatum_weight_split (S : SieveDatum) {m : ℕ} (u : Fin m → ℕ) (d : ℕ) :
    (if (∀ i, 1 ≤ (Fin.snoc u d : Fin (m + 1) → ℕ) i) then
        (∏ i, S.h ((Fin.snoc u d : Fin (m + 1) → ℕ) i))
      else 0) = (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) *
        (if 1 ≤ d then S.h d else 0) := by
  have hcond1 : (∀ i, 1 ≤ (Fin.snoc u d : Fin (m + 1) → ℕ) i) ↔ (∀ i, 1 ≤ u i) ∧ 1 ≤ d := by
    rw [Fin.forall_fin_succ']
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  by_cases hu : (∀ i, 1 ≤ u i)
  · by_cases hd : 1 ≤ d
    · rw [if_pos (hcond1.mpr ⟨hu, hd⟩), if_pos hu, if_pos hd, Fin.prod_univ_castSucc]
      simp only [Fin.snoc_castSucc, Fin.snoc_last]
    · rw [if_neg fun h ↦ hd (hcond1.mp h).2, if_neg hd, mul_zero]
  · rw [if_neg fun h ↦ hu (hcond1.mp h).1, if_neg hu, zero_mul]

/-- **Collapse of the empty remaining integral.**  With all `n` coordinates pinned by `u`, the
indicator integrand over the unit cube is the constant `(F (toLp 2 a)) ^ 2` — the simplex
condition either holds or `F` vanishes there — and the cube has volume `1`. -/
private theorem sieveE_inner_pinned_eq {n : ℕ} (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : Function.support F ⊆ 𝓡 n) (u : Fin n → ℕ) :
    (∫ x in Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1), Set.indicator
          {y : Fin n → ℝ |
            ∑ i : Fin n, (if h : (i : ℕ) < n then
                    Real.log (u ⟨i, h⟩) / Real.log z
                  else y i) ≤ 1}
          (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < n then
                  Real.log (u ⟨i, h⟩) / Real.log z
                else y i))) ^ 2) x) =
      (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log z))) ^ 2 := by
  have hxsub : ∀ x : Fin n → ℝ, (fun i : Fin n ↦ if h : (i : ℕ) < n then
      Real.log (u ⟨i, h⟩) / Real.log z else x i) = fun i ↦ Real.log (u i) / Real.log z :=
    fun x ↦ funext fun i ↦ dif_pos i.isLt
  simp only [hxsub]
  by_cases hP : ∑ i : Fin n, Real.log (u i) / Real.log z ≤ 1
  · rw [show {y : Fin n → ℝ | ∑ i, Real.log (u i) / Real.log z ≤ 1} = Set.univ from
        Set.eq_univ_of_forall fun _ ↦ hP, Set.indicator_univ, MeasureTheory.setIntegral_const,
      MeasureTheory.measureReal_def, MeasureTheory.volume_pi_pi]
    simp [Real.volume_Icc]
  · rw [not_le] at hP
    rw [eq_zero_of_notMem_R hsupp (notMem_R_of_one_lt_sum hP)]
    simp

/-- (density-agnostic port of `S1E_full`). The empty remaining integral collapses to the point
evaluation.
-/
theorem sieveE_full {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : Function.support F ⊆ 𝓡 n) :
    sieveE S z F n = ∑' u : Fin n → ℕ, if (∀ i, 1 ≤ u i) then
            (∏ i, S.h (u i)) * (F (WithLp.toLp 2 (fun i ↦ Real.log (u i) / Real.log z))) ^ 2
          else 0 := by
  unfold sieveE
  refine tsum_congr fun u ↦ ?_
  rw [Nat.sub_self, pow_zero, mul_one, sieveE_inner_pinned_eq z F hsupp u]
  by_cases hcond : (∀ i, 1 ≤ u i)
  · rw [if_pos hcond, if_pos hcond]
  · rw [if_neg hcond, if_neg hcond, zero_mul]

/-- (density-agnostic port of `S1_layer_Em_expand`). The `S1_datum_facts` /`rw [hSS]` step vanishes
since `sieveE` already carries `𝔖 S.γ`.
-/
theorem sieveE_Em_expand {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 n) (m : ℕ) (hm : m < n) :
    sieveE S z F m = ((PrimeGaps.singularSeries S.γ) * Real.log z) ^ (n - m - 1) * ∑' u : Fin m → ℕ,
            (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) *
            (PrimeGaps.singularSeries S.γ * Real.log z * ∫ s in (0 : ℝ)..1, layerG z F u s) := by
  unfold sieveE
  rw [← tsum_mul_left]
  refine tsum_congr fun u ↦ ?_
  rw [S1Em_inner_eq_layerG_int hm z F hF hsupp u]
  conv_lhs => rw [show n - m = (n - m - 1) + 1 by omega]
  rw [pow_succ]
  ring

/-- If some coordinate of the prefix `u` exceeds `⌈z⌉₊`, the layer function `layerG z F u`
vanishes identically: the pinned coordinate `log (u j) / log z` already exceeds `1`, so the
substituted point lies outside the simplex `𝓡 n`. -/
theorem layerG_eq_zero_of_notMem_box {n m : ℕ} (z : ℝ) (hz : 2 ≤ z)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : Function.support F ⊆ 𝓡 n) (hm : m < n)
    (u : Fin m → ℕ)
    (hu : u ∉ Fintype.piFinset (fun _ : Fin m ↦ Finset.range (⌈z⌉₊ + 1))) (s : ℝ) :
    layerG z F u s = 0 := by
  rw [Fintype.mem_piFinset] at hu
  push Not at hu
  obtain ⟨j, hj⟩ := hu
  simp only [Finset.mem_range, not_lt] at hj
  refine S1_layerG_eq_zero_of_coord_ge hm z F hsupp u s hz j ?_
  linarith [Nat.le_ceil z, (by exact_mod_cast hj : (⌈z⌉₊ + 1 : ℝ) ≤ (u j : ℝ))]

/-- Summability of the reindexed `sieveE … (m+1)` outer weight (finite support:
`layerG z F u (log d/log z) = 0` unless every `u i < z`).
-/
theorem sieveE_summable_Td {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : Function.support F ⊆ 𝓡 n)
    (m : ℕ) (hm : m < n) (hz : 2 ≤ z) :
    Summable (fun u : Fin m → ℕ ↦ (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) *
      (∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
            S.h d * layerG z F u (Real.log ↑d / Real.log z))) := by
  apply summable_of_ne_finset_zero (s := Fintype.piFinset (fun _ : Fin m ↦ Finset.range (⌈z⌉₊ + 1)))
  intro u hu
  simp only [layerG_eq_zero_of_notMem_box z hz F hsupp hm u hu, mul_zero, Finset.sum_const_zero]

/-- Summability of the `sieveE … m` outer weight (same finite support argument). -/
theorem sieveE_summable_Ig {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hsupp : Function.support F ⊆ 𝓡 n)
    (m : ℕ) (hm : m < n) (hz : 2 ≤ z) :
    Summable (fun u : Fin m → ℕ ↦
      (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) * (PrimeGaps.singularSeries S.γ *
        Real.log z *
          ∫ s in (0 : ℝ)..1, layerG z F u s)) := by
  apply summable_of_ne_finset_zero (s := Fintype.piFinset (fun _ : Fin m ↦ Finset.range (⌈z⌉₊ + 1)))
  intro u hu
  simp only [layerG_eq_zero_of_notMem_box z hz F hsupp hm u hu, intervalIntegral.integral_zero,
    mul_zero]

/-- `S.h 0 = 0` (since `μ(0) = 0`). -/
theorem sieveDatum_h_zero (S : SieveDatum) : S.h 0 = 0 := by
  simp [SieveDatum.h]

/-- (density-agnostic port of `S1_layer_Em1_expand`). Reindex the tsum over `Fin (m+1) → ℕ` as
`(Fin m → ℕ) × ℕ` (`Fin.snoc`); the weight product splits (`sieveDatum_weight_split`), the extra
power factors out, the inner cube integral is `layerG` (`S1Em1_inner_eq_layerG`), and the sum over
`d` collapses to the finite `∑_{0<d<z}` because `layerG` vanishes for `d ≥ z`. No `S1_datum_facts`:
the inner weight is already `S.h d`.
-/
theorem sieveE_Em1_expand {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 n) (m : ℕ) (hm : m < n) (hz : 2 ≤ z) :
    sieveE S z F (m + 1) = ((PrimeGaps.singularSeries S.γ) * Real.log z) ^ (n - m - 1) *
        ∑' u : Fin m → ℕ, (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) *
            (∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
                  S.h d * layerG z F u (Real.log ↑d / Real.log z)) := by
  set A := (PrimeGaps.singularSeries S.γ) * Real.log z with hAdef
  set e : (Fin m → ℕ) × ℕ ≃ (Fin (m + 1) → ℕ) :=
    (Equiv.prodComm (Fin m → ℕ) ℕ).trans (Fin.snocEquiv (fun _ ↦ ℕ))
  have hepp : ∀ p : (Fin m → ℕ) × ℕ, e p = Fin.snoc p.1 p.2 := fun _ ↦ rfl
  unfold sieveE
  rw [← Equiv.tsum_eq e]
  have hsummand : ∀ p : (Fin m → ℕ) × ℕ, ((if (∀ i, 1 ≤ (e p) i) then (∏ i, S.h ((e p) i)) else 0) *
        ((PrimeGaps.singularSeries S.γ) * Real.log z) ^ (n - (m + 1)) *
        (∫ x in Set.pi Set.univ (fun _ : Fin n ↦ Set.Icc (0 : ℝ) 1), Set.indicator
                {y : Fin n → ℝ |
                  ∑ i : Fin n, (if h : (i : ℕ) < m + 1 then
                          Real.log ((e p) ⟨i, h⟩) / Real.log z
                        else y i) ≤ 1}
                (fun y ↦ (F (WithLp.toLp 2 (fun i ↦ if h : (i : ℕ) < m + 1 then
                        Real.log ((e p) ⟨i, h⟩) / Real.log z
                      else y i))) ^ 2) x)) = A ^ (n - m - 1) *
        ((if (∀ i, 1 ≤ p.1 i) then (∏ i, S.h (p.1 i)) else 0) * ((if 1 ≤ p.2 then S.h p.2 else 0) *
            layerG z F p.1 (Real.log p.2 / Real.log z))) := by
    rintro ⟨u, d⟩
    simp only [hepp]
    rw [show n - (m + 1) = n - m - 1 by omega, S1Em1_inner_eq_layerG z F hsupp u d,
      sieveDatum_weight_split S u d, ← hAdef]
    ring
  rw [tsum_congr hsummand, tsum_mul_left]
  congr 1
  have hR0 : (0 : ℝ) < Real.log z := Real.log_pos (by linarith)
  set G : (Fin m → ℕ) → ℕ → ℝ := fun u d ↦ layerG z F u (Real.log d / Real.log z) with hG
  have hdpt : ∀ (u : Fin m → ℕ) (d : ℕ), (if 1 ≤ d then S.h d else 0) * G u d = S.h d * G u d := by
    intro u d
    by_cases hd : 1 ≤ d
    · rw [if_pos hd]
    · obtain rfl : d = 0 := by omega
      rw [if_neg hd, sieveDatum_h_zero]
  have hfin : ∀ (u : Fin m → ℕ) (d : ℕ),
      d ∉ {d ∈ Finset.range ⌈z⌉₊ | (0 : ℕ) < d ∧ (↑d : ℝ) < z} →
      S.h d * G u d = 0 := by
    have hbig : ∀ (u : Fin m → ℕ) (d : ℕ), z ≤ (d : ℝ) → S.h d * G u d = 0 := by
      intro u d hd
      simp only [hG]
      rw [S1_layerG_eq_zero_of_arg_ge_one hm z F hF hsupp u _ hz
        (by rw [le_div_iff₀ hR0, one_mul]; exact Real.log_le_log (by linarith) hd)]
      ring
    intro u d hd
    rw [Finset.mem_filter, not_and_or] at hd
    rcases hd with hrange | hcond
    · rw [Finset.mem_range, not_lt] at hrange
      exact hbig u d (le_trans (Nat.le_ceil _) (by exact_mod_cast hrange))
    · rw [not_and_or] at hcond
      rcases hcond with h0 | hlt
      · obtain rfl : d = 0 := by omega
        rw [sieveDatum_h_zero]
        ring
      · exact hbig u d (not_lt.mp hlt)
  have hfiber : ∀ u : Fin m → ℕ,
      (∑' d : ℕ, (if 1 ≤ d then S.h d else 0) * G u d) =
        ∑ d ∈ {d ∈ Finset.range ⌈z⌉₊ | (0 : ℕ) < d ∧ (↑d : ℝ) < z},
            S.h d * G u d := fun u ↦ by
    rw [tsum_congr (fun d ↦ hdpt u d)]
    exact tsum_eq_sum (fun d hd ↦ hfin u d hd)
  have hsumd : ∀ u : Fin m → ℕ, Summable (fun d : ℕ ↦
      (if 1 ≤ d then S.h d else 0) * G u d) := fun u ↦ by
    apply summable_of_ne_finset_zero
      (s := {d ∈ Finset.range ⌈z⌉₊ | (0 : ℕ) < d ∧ (↑d : ℝ) < z})
    intro d hd
    rw [hdpt u d]
    exact hfin u d hd
  set wt : (Fin m → ℕ) → ℝ := fun u ↦ (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0)
  have hsumprod : Summable (fun x : (Fin m → ℕ) × ℕ ↦
      wt x.1 * ((if 1 ≤ x.2 then S.h x.2 else 0) * G x.1 x.2)) := by
    apply summable_of_ne_finset_zero
      (s := (Fintype.piFinset (fun _ : Fin m ↦ Finset.range (⌈z⌉₊ + 1))) ×ˢ
            {d ∈ Finset.range ⌈z⌉₊ | (0 : ℕ) < d ∧ (↑d : ℝ) < z})
    intro x hx
    rw [Finset.mem_product, not_and_or] at hx
    rcases hx with hu | hd
    · simp only [hG]
      rw [layerG_eq_zero_of_notMem_box z hz F hsupp hm x.1 hu]
      ring
    · rw [hdpt x.1 x.2, hfin x.1 x.2 hd, mul_zero]
  rw [Summable.tsum_prod' hsumprod fun u ↦ (hsumd u).mul_left (wt u)]
  refine tsum_congr fun u ↦ ?_
  dsimp only
  rw [tsum_mul_left, hfiber u]

/-- (density-agnostic port of `S1_layer_identity`).
`sieveE(m+1) − sieveE(m) = (𝔖 S.γ · log z)^{n-m-1} · ∑'_u (∏ S.h) · (Td − Ig)`.
-/
theorem sieveE_layer_identity {n : ℕ} (S : SieveDatum) (z : ℝ)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 n) (m : ℕ) (hm : m < n) (hz : 2 ≤ z) :
    sieveE S z F (m + 1) - sieveE S z F m =
      ((PrimeGaps.singularSeries S.γ) * Real.log z) ^ (n - m - 1) * ∑' u : Fin m → ℕ,
            (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) *
            ((∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
                  S.h d * layerG z F u (Real.log ↑d / Real.log z)) -
                PrimeGaps.singularSeries S.γ * Real.log z * ∫ s in (0 : ℝ)..1, layerG z F u s) := by
  set A : ℝ := (PrimeGaps.singularSeries S.γ) * Real.log z
  set wt : (Fin m → ℕ) → ℝ := fun u ↦ (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0)
  set Td : (Fin m → ℕ) → ℝ := fun u ↦ ∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
        S.h d * layerG z F u (Real.log ↑d / Real.log z)
  set Ig : (Fin m → ℕ) → ℝ := fun u ↦
      PrimeGaps.singularSeries S.γ * Real.log z * ∫ s in (0 : ℝ)..1, layerG z F u s
  have hEm1 : sieveE S z F (m + 1) = A ^ (n - m - 1) * ∑' u : Fin m → ℕ, wt u * Td u :=
    sieveE_Em1_expand S z F hF hsupp m hm hz
  have hEm : sieveE S z F m = A ^ (n - m - 1) * ∑' u : Fin m → ℕ, wt u * Ig u :=
    sieveE_Em_expand S z F hF hsupp m hm
  rw [hEm1, hEm, ← mul_sub]
  congr 1
  rw [← Summable.tsum_sub (sieveE_summable_Td S z F hsupp m hm hz)
    (sieveE_summable_Ig S z F hsupp m hm hz)]
  exact tsum_congr fun u ↦ by rw [← mul_sub]

/-- The outer weight sum over the box `{u: ∀ i, uᵢ ≤ ⌈z⌉}` factors as the `m` -th power of the
single-coordinate partial sum `∑_{d < ⌈z⌉+1} S.h d`.
-/
theorem sieveDatum_boxsum_eq (S : SieveDatum) (z : ℝ) {m : ℕ} :
    ∑ u ∈ Fintype.piFinset (fun _ : Fin m ↦ Finset.range (⌈z⌉₊ + 1)),
        (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) =
      (∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d) ^ m := by
  have hwt : ∀ u : Fin m → ℕ,
      (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) = ∏ i, S.h (u i) := by
    intro u
    by_cases h1 : ∀ i, 1 ≤ u i
    · rw [if_pos h1]
    · rw [if_neg h1]
      push Not at h1
      obtain ⟨j, hj⟩ := h1
      exact (Finset.prod_eq_zero (Finset.mem_univ j)
        (by rw [show u j = 0 by omega]; exact sieveDatum_h_zero S)).symm
  rw [Finset.sum_congr rfl (fun u _ ↦ hwt u),
    ← Finset.prod_univ_sum (fun _ : Fin m ↦ Finset.range (⌈z⌉₊ + 1)) (fun _ d ↦ S.h d),
    Finset.prod_const, Finset.card_univ, Fintype.card_fin]

end PrimeGaps
