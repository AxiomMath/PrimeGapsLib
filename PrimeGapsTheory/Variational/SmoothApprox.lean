/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.Analysis.Normed.Lp.SmoothApprox
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Dynamics.Ergodic.Action.Regular
public import Mathlib.Geometry.Manifold.PartitionOfUnity
public import Mathlib.Geometry.Manifold.Sheaf.Basic
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.Order.CompletePartialOrder
public import PrimeGapsTheory.Analysis.Simplex

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Smooth approximation on the simplex

Constructs smooth cutoffs on a simplex and smooth approximations to bounded square-integrable
functions supported there.

## Main definitions

* `RkEps`: The simplex obtained by imposing an epsilon margin on every boundary inequality.
* `simplexPi`: The standard simplex in a finite real product.

## Main results

* `exists_smooth_simplex_cutoff`: Gives a smooth simplex cutoff with a truncation bound.
* `smooth_L2_approx_on_simplex`: Approximates bounded square-integrable functions by smooth
  simplex-supported functions.
-/

@[expose] public section

open scoped Manifold

open MeasureTheory Set EuclideanSpace
open scoped PrimeGaps

namespace PrimeGaps

/-- Every coordinate of a point of `𝓡 k` lies in `[0,1]`: it is nonnegative, and it is bounded by
the sum of the coordinates, which is at most `1`. -/
lemma coord_mem_Icc_of_mem_R {k : ℕ} {x : EuclideanSpace ℝ (Fin k)} (hx : x ∈ 𝓡 k) (i : Fin k) :
    x.ofLp i ∈ Set.Icc (0 : ℝ) 1 := by
  rw [EuclideanSpace.mem_scaledStdSimplex_iff] at hx
  obtain ⟨hnn, hsum⟩ := hx
  refine ⟨hnn i, ?_⟩
  have hle : x.ofLp i ≤ ∑ j, x.ofLp j := Finset.single_le_sum (fun j _ ↦ hnn j) (Finset.mem_univ i)
  linarith

/-- The inner `ε`-shrunken simplex `{ t : t_i ≥ ε for all i, ∑ t_i ≤ 1 - ε }`. -/
def RkEps (k : ℕ) (ε : ℝ) : Set (EuclideanSpace ℝ (Fin k)) :=
  {x | (∀ i, ε ≤ x i) ∧ (∑ i, x i) ≤ 1 - ε}

/-- The pi-Lebesgue standard simplex over `Fin n → ℝ`. -/
def simplexPi (n : ℕ) (a : ℝ) : Set (Fin n → ℝ) :=
  {x | (∀ i, 0 ≤ x i) ∧ (∑ i, x i) ≤ a}

/-- `simplexPi n a` is measurable, being an intersection of closed half-spaces. -/
lemma measurableSet_simplexPi (n : ℕ) (a : ℝ) : MeasurableSet (simplexPi n a) := by
  have h1 : MeasurableSet (⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i}) := MeasurableSet.iInter fun i ↦
    measurableSet_le measurable_const (measurable_pi_apply i)
  have h2 : MeasurableSet {x : Fin n → ℝ | (∑ i, x i) ≤ a} :=
    measurableSet_le (Finset.measurable_sum _ (fun i _ ↦ measurable_pi_apply i)) measurable_const
  have : simplexPi n a =
      (⋂ i : Fin n, {x : Fin n → ℝ | 0 ≤ x i}) ∩ {x : Fin n → ℝ | (∑ i, x i) ≤ a} := by
    ext x; simp only [simplexPi, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
  rw [this]; exact h1.inter h2

section

open scoped Nat

/-- Exact volume of the pi-Lebesgue simplex for `a ≥ 0`. -/
lemma simplexPi_volume (n : ℕ) (a : ℝ) (ha : 0 ≤ a) :
    volume (simplexPi n a) = ENNReal.ofReal (a ^ n / (n ! : ℝ)) := by
  induction n generalizing a with
  | zero =>
    have huniv : simplexPi 0 a = Set.univ := by
      ext x
      simp only [simplexPi, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
      refine ⟨fun i ↦ i.elim0, ?_⟩
      simpa using ha
    rw [huniv]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one]
    rw [volume_pi]
    exact Measure.pi_empty_univ _
  | succ n ih =>
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0 with he
    have hmp := measurePreserving_piFinSuccAbove
      (fun _ : Fin (n + 1) ↦ (volume : Measure ℝ)) (0 : Fin (n + 1))
    have hsymm (t : ℝ) (y : Fin n → ℝ) : e.symm (t, y) = Fin.cons t y := by
      rw [show e.symm (t, y) = Fin.insertNth 0 t y from rfl, Fin.insertNth_zero']
    have himg : e '' simplexPi (n + 1) a =
        {p : ℝ × (Fin n → ℝ) | 0 ≤ p.1 ∧ (∀ j, 0 ≤ p.2 j) ∧ p.1 + ∑ j, p.2 j ≤ a} := by
      ext ⟨t, y⟩
      simp only [Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨x, hx, hxe⟩
        have hxx : x = e.symm (t, y) := by rw [← hxe]; exact (e.symm_apply_apply x).symm
        rw [hxx, hsymm] at hx
        simpa only [simplexPi, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
          Fin.cons_succ, Fin.sum_univ_succ, and_assoc] using hx
      · intro hp
        refine ⟨e.symm (t, y), ?_, ?_⟩
        · rw [hsymm]
          simpa only [simplexPi, Set.mem_ofPred_eq, Fin.forall_fin_succ, Fin.cons_zero,
            Fin.cons_succ, Fin.sum_univ_succ, and_assoc] using hp
        · exact e.apply_symm_apply (t, y)
    have hmeasS : MeasurableSet (simplexPi (n + 1) a) := measurableSet_simplexPi (n + 1) a
    have hmeasImg : MeasurableSet (e '' simplexPi (n + 1) a) := e.measurableSet_image.mpr hmeasS
    have hstep1 : volume (simplexPi (n + 1) a) =
        (volume.prod (Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ)))
            (e '' simplexPi (n + 1) a) := by
      rw [volume_pi, ← hmp.measure_preimage hmeasImg.nullMeasurableSet]
      congr 1
      rw [Set.preimage_image_eq _ e.injective]
    rw [hstep1, Measure.prod_apply hmeasImg]
    have hslice : ∀ t : ℝ, (Measure.pi fun _ : Fin n ↦ (volume : Measure ℝ))
            (Prod.mk t ⁻¹' (e '' simplexPi (n + 1) a)) = (Set.Icc (0 : ℝ) a).indicator
              (fun t ↦ ENNReal.ofReal ((a - t) ^ n / (n ! : ℝ))) t := by
      intro t
      have hpre : Prod.mk t ⁻¹' (e '' simplexPi (n + 1) a) =
          {y : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ y j) ∧ t + ∑ j, y j ≤ a} := by
        rw [himg]; ext y; simp only [Set.mem_preimage, Set.mem_ofPred_eq]
      rw [hpre]
      by_cases ht0 : 0 ≤ t
      · by_cases hta : t ≤ a
        · have hslice_eq : {y : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ y j) ∧ t + ∑ j, y j ≤ a} =
              simplexPi n (a - t) := by
            ext y
            simp only [simplexPi, Set.mem_ofPred_eq]
            constructor
            · rintro ⟨_, hy, hs⟩; exact ⟨hy, by linarith⟩
            · rintro ⟨hy, hs⟩; exact ⟨ht0, hy, by linarith⟩
          rw [hslice_eq, ← volume_pi, ih (a - t) (by linarith)]
          rw [Set.indicator_of_mem (Set.mem_Icc.mpr ⟨ht0, hta⟩)]
        · have hempty : {y : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ y j) ∧ t + ∑ j, y j ≤ a} = ∅ := by
            ext y
            simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
            intro _ hy
            have : (0 : ℝ) ≤ ∑ j, y j := Finset.sum_nonneg (fun j _ ↦ hy j)
            linarith
          rw [hempty, measure_empty, Set.indicator_of_notMem]
          simp only [Set.mem_Icc, not_and, not_le]; intro _; linarith
      · have hempty : {y : Fin n → ℝ | 0 ≤ t ∧ (∀ j, 0 ≤ y j) ∧ t + ∑ j, y j ≤ a} = ∅ := by
          ext y
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
          intro h; exact absurd h ht0
        rw [hempty, measure_empty, Set.indicator_of_notMem]
        simp only [Set.mem_Icc, not_and, not_le]; intro h; exact absurd h ht0
    simp_rw [hslice]
    have hmeasIcc : MeasurableSet (Set.Icc (0 : ℝ) a) := measurableSet_Icc
    rw [lintegral_indicator hmeasIcc]
    set g : ℝ → ℝ := fun t ↦ (a - t) ^ n / (n ! : ℝ) with hg
    have hcont : Continuous g := ((continuous_const.sub continuous_id).pow n).div_const _
    have hintg : IntegrableOn g (Set.Icc (0 : ℝ) a) volume := hcont.integrableOn_Icc
    have hnn : 0 ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) a)] g := by
      filter_upwards [ae_restrict_mem hmeasIcc] with x hx
      simp only [hg]
      have : (0 : ℝ) ≤ a - x := by
        rw [Set.mem_Icc] at hx; linarith [hx.2]
      positivity
    rw [← ofReal_integral_eq_lintegral_ofReal hintg hnn]
    congr 1
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le ha]
    have hpow : ∫ x in (0 : ℝ)..a, (a - x) ^ n = a ^ (n + 1) / (n + 1) := by
      rw [intervalIntegral.integral_comp_sub_left (fun u ↦ u ^ n) a]
      simp only [sub_self, sub_zero]
      rw [integral_pow]
      simp
    calc ∫ x in (0 : ℝ)..a, g x = (∫ x in (0 : ℝ)..a, (a - x) ^ n) / (n ! : ℝ) := by
          simp only [hg]; rw [intervalIntegral.integral_div]
      _ = (a ^ (n + 1) / (n + 1)) / (n ! : ℝ) := by rw [hpow]
      _ = a ^ (n + 1) / ((n + 1)! : ℝ) := by
          rw [Nat.factorial_succ]
          push_cast
          field_simp

end

/-- The Lebesgue volume of the standard simplex `𝓡 k` is at most `1 / k!`. -/
lemma R_volume_le (k : ℕ) : (volume (𝓡 k)).toReal ≤ 1 / (k.factorial : ℝ) := by
  have hmp := EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin k)
  set φ := (MeasurableEquiv.toLp 2 (Fin k → ℝ)).symm with hφ
  have hpre : 𝓡 k = φ ⁻¹' (simplexPi k 1) := by
    ext x
    rw [EuclideanSpace.mem_scaledStdSimplex_iff]
    simp only [simplexPi, Set.mem_preimage, Set.mem_ofPred_eq]
    rfl
  have hvol : volume (𝓡 k) = volume (simplexPi k 1) := by
    rw [hpre]
    exact hmp.measure_preimage (measurableSet_simplexPi k 1).nullMeasurableSet
  rw [hvol, simplexPi_volume k 1 (by norm_num), ENNReal.toReal_ofReal (by positivity)]
  simp only [one_pow, le_refl]

open scoped Nat

open scoped Pointwise in
/-- The volume of `RkEps k ε` is `(1 - (k + 1) * ε) ^ k` times the volume of `𝓡 k`. -/
lemma RkEps_volume (k : ℕ) (ε : ℝ) (hc : 0 ≤ 1 - (k + 1) * ε) :
    volume (RkEps k ε) = ENNReal.ofReal ((1 - (k + 1) * ε) ^ k) * volume (𝓡 k) := by
  set c : ℝ := 1 - (k + 1) * ε with hcdef
  set v : EuclideanSpace ℝ (Fin k) := WithLp.toLp 2 (fun _ ↦ ε) with hvdef
  have hcnn : 0 ≤ c := hc
  have hvcoord : ∀ i, v i = ε := fun i ↦ rfl
  have hset : RkEps k ε = (fun x : EuclideanSpace ℝ (Fin k) ↦ v + c • x) '' 𝓡 k := by
    ext z
    simp only [RkEps, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨hz1, hz2⟩
      by_cases hc0 : c = 0
      · refine ⟨0, EuclideanSpace.mem_scaledStdSimplex_iff.mpr
          ⟨fun i ↦ le_refl 0, by simp⟩, ?_⟩
        rw [hc0]
        simp only [zero_smul, add_zero]
        have hkε : (k : ℝ) * ε = 1 - ε := by
          have : (↑k + 1) * ε = 1 := by linarith [hc0, hcdef]
          nlinarith [this]
        have hsumge : (k : ℝ) * ε ≤ ∑ i, z i :=
          calc (k : ℝ) * ε = ∑ _ : Fin k, ε := by
                rw [Finset.sum_const]; simp [mul_comm]
            _ ≤ ∑ i, z i := Finset.sum_le_sum (fun i _ ↦ hz1 i)
        have hsumeq : ∑ i, z i = (k : ℝ) * ε := le_antisymm (by linarith [hz2, hkε]) hsumge
        have hzeq : ∀ i, z i = ε := by
          intro i
          by_contra hne
          have hlt : ε < z i := lt_of_le_of_ne (hz1 i) (Ne.symm hne)
          have : (k : ℝ) * ε < ∑ i, z i :=
            calc (k : ℝ) * ε = ∑ _ : Fin k, ε := by rw [Finset.sum_const]; simp [mul_comm]
              _ < ∑ j, z j := by
                  exact Finset.sum_lt_sum (fun j _ ↦ hz1 j) ⟨i, Finset.mem_univ i, hlt⟩
          linarith [hsumeq]
        ext i
        rw [hvcoord i, hzeq i]
      · have hcpos : 0 < c := lt_of_le_of_ne hcnn (Ne.symm hc0)
        refine ⟨c⁻¹ • (z - v), EuclideanSpace.mem_scaledStdSimplex_iff.mpr ⟨?_, ?_⟩, ?_⟩
        · intro i
          simp only [PiLp.smul_apply, PiLp.sub_apply, hvcoord, smul_eq_mul]
          have : ε ≤ z i := hz1 i
          have hnn2 : 0 ≤ z i - ε := by linarith
          positivity
        · simp only [PiLp.smul_apply, PiLp.sub_apply, hvcoord, smul_eq_mul]
          rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const]
          simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [inv_mul_le_iff₀ hcpos]
          have hsum : ∑ i, z i ≤ 1 - ε := hz2
          have : (k : ℝ) * ε + c = 1 - ε := by rw [hcdef]; ring
          nlinarith [hsum, this]
        · ext i
          simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, hvcoord, smul_eq_mul]
          field_simp
          ring
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨hx1, hx2⟩ := EuclideanSpace.mem_scaledStdSimplex_iff.mp hx
      refine ⟨?_, ?_⟩
      · intro i
        simp only [PiLp.add_apply, PiLp.smul_apply, hvcoord, smul_eq_mul]
        have : 0 ≤ c * x i := mul_nonneg hcnn (hx1 i)
        linarith
      · simp only [PiLp.add_apply, PiLp.smul_apply, hvcoord, smul_eq_mul]
        rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum]
        simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        have hcx : c * ∑ i, x i ≤ c * 1 := mul_le_mul_of_nonneg_left hx2 hcnn
        have : (k : ℝ) * ε + c = 1 - ε := by rw [hcdef]; ring
        nlinarith [hcx, this]
  rw [hset]
  have himg2 : (fun x : EuclideanSpace ℝ (Fin k) ↦ v + c • x) '' 𝓡 k = v +ᵥ (c • 𝓡 k) := by
    ext z
    simp only [Set.mem_image, Set.mem_vadd_set, Set.mem_smul_set, vadd_eq_add]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨c • x, ⟨x, hx, rfl⟩, rfl⟩
    · rintro ⟨w, ⟨x, hx, rfl⟩, rfl⟩
      exact ⟨x, hx, rfl⟩
  rw [himg2, measure_vadd, Measure.addHaar_smul_of_nonneg volume hcnn (𝓡 k),
    finrank_euclideanSpace, Fintype.card_fin]

/-- For integers `k ≥ 2`, `k * (k + 1) / k! ≤ 2 * k`, equivalently `(k+1)/(k-1)! ≤ 2k`. -/
lemma factorial_arith_bound (k : ℕ) (hk : 2 ≤ k) :
    (k : ℝ) * (k + 1) / (k ! : ℝ) ≤ 2 * k := by
  have hfac_pos : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
  rw [div_le_iff₀ hfac_pos]
  have hk_le : (k : ℝ) ≤ (k ! : ℝ) := by exact_mod_cast Nat.self_le_factorial k
  have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  nlinarith [hk_le, hk2]

/-- For `k ≥ 2` and `ε ∈ (0, 1/(2k))` there is a smooth function `χ` valued in `[0,1]` that equals
`1` on the inner simplex `R_k^(ε)`, vanishes outside `R_k`, and truncates any bounded measurable
`G` (with `|G| ≤ M` on `R_k`) with squared `L²` error at most `M² · vol(R_k \ R_k^(ε)) ≤ M² · 2kε`.
-/
@[pg_tag "bg246" "lem_smooth_cutoff_simplex"]
theorem exists_smooth_simplex_cutoff (k : ℕ) (hk : 2 ≤ k) (ε : ℝ) (hε : 0 < ε)
    (hε2 : ε < 1 / (2 * k)) :
    ∃ χ : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ t, χ t ∈ Set.Icc (0 : ℝ) 1) ∧
      (∀ t ∈ RkEps k ε, χ t = 1) ∧
      (∀ t ∉ 𝓡 k, χ t = 0) ∧
      (∀ (G : EuclideanSpace ℝ (Fin k) → ℝ) (M : ℝ), Measurable G → 0 ≤ M → (∀ t ∈ 𝓡 k, |G t| ≤ M) →
        (∫ t in 𝓡 k, (G t - G t * χ t) ^ 2) ≤ M ^ 2 * (volume (𝓡 k \ RkEps k ε)).toReal ∧
          M ^ 2 * (volume (𝓡 k \ RkEps k ε)).toReal ≤ M ^ 2 * (2 * k * ε)) := by
  have hcoord : ∀ i : Fin k, Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦ x i) :=
    fun i ↦ (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  have hsum : Continuous (fun x : EuclideanSpace ℝ (Fin k) ↦ ∑ i, x i) :=
    continuous_finsetSum _ (fun i _ ↦ hcoord i)
  have hclosedEps : IsClosed (RkEps k ε) := by
    have h1 : IsClosed (⋂ i : Fin k, {x : EuclideanSpace ℝ (Fin k) | ε ≤ x i}) :=
      isClosed_iInter (fun i ↦ isClosed_le continuous_const (hcoord i))
    have h2 : IsClosed {x : EuclideanSpace ℝ (Fin k) | (∑ i, x i) ≤ 1 - ε} :=
      isClosed_le hsum continuous_const
    have : RkEps k ε = (⋂ i : Fin k, {x : EuclideanSpace ℝ (Fin k) | ε ≤ x i}) ∩
          {x : EuclideanSpace ℝ (Fin k) | (∑ i, x i) ≤ 1 - ε} := by
      ext x
      simp only [RkEps, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
    rw [this]
    exact h1.inter h2
  have hclosedRk : IsClosed (𝓡 k) := isClosed_scaledStdSimplex
  have hsub : RkEps k ε ⊆ interior (𝓡 k) := by
    set U : Set (EuclideanSpace ℝ (Fin k)) :=
      (⋂ i : Fin k, {x | 0 < x i}) ∩ {x | (∑ i, x i) < 1} with hU
    have hUopen : IsOpen U :=
      (isOpen_iInter_of_finite fun i ↦ isOpen_lt continuous_const (hcoord i)).inter
        (isOpen_lt hsum continuous_const)
    have hUsub : U ⊆ 𝓡 k := by
      intro x hx
      simp only [hU, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hx
      exact EuclideanSpace.mem_scaledStdSimplex_iff.mpr ⟨fun i ↦ (hx.1 i).le, hx.2.le⟩
    have hEpsU : RkEps k ε ⊆ U := by
      intro x hx
      obtain ⟨hx1, hx2⟩ := hx
      simp only [hU, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
      refine ⟨fun i ↦ lt_of_lt_of_le hε (hx1 i), ?_⟩
      have : (∑ i, x i) ≤ 1 - ε := hx2
      linarith
    calc RkEps k ε ⊆ U := hEpsU
      _ = interior U := (hUopen.interior_eq).symm
      _ ⊆ interior (𝓡 k) := interior_mono hUsub
  have hdisj : Disjoint (interior (𝓡 k))ᶜ (RkEps k ε) := by
    rwa [Set.disjoint_compl_left_iff_subset]
  obtain ⟨f, hf0, hf1, hfIcc⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
      (I := 𝓘(ℝ, (EuclideanSpace ℝ (Fin k)))) (n := (⊤ : ℕ∞))
      (isOpen_interior.isClosed_compl) hclosedEps hdisj
  refine ⟨⇑f, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← contMDiff_iff_contDiff]
    exact f.contMDiff
  · exact hfIcc
  · exact fun t ht ↦ hf1.self_of_nhdsSet t ht
  · intro t ht
    have hmem : t ∈ (interior (𝓡 k))ᶜ := by
      simp only [Set.mem_compl_iff]
      exact fun hc ↦ ht (interior_subset hc)
    exact hf0.self_of_nhdsSet t hmem
  · have hmeasRk : MeasurableSet (𝓡 k) := hclosedRk.measurableSet
    have hmeasEps : MeasurableSet (RkEps k ε) := hclosedEps.measurableSet
    have hRkball : 𝓡 k ⊆ Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1 := by
      intro x hx
      obtain ⟨hx0, hxs⟩ := EuclideanSpace.mem_scaledStdSimplex_iff.mp hx
      rw [Metric.mem_closedBall, dist_zero_right]
      rw [EuclideanSpace.norm_eq, show (1 : ℝ) = √1 by simp]
      apply Real.sqrt_le_sqrt
      calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, x i := by
            apply Finset.sum_le_sum
            intro i _
            rw [Real.norm_eq_abs, sq_abs]
            have hxi : 0 ≤ x i := hx0 i
            have hxile : x i ≤ 1 := by
              have : x i ≤ ∑ j, x j := Finset.single_le_sum (fun j _ ↦ hx0 j) (Finset.mem_univ i)
              linarith
            nlinarith [hxi, hxile]
        _ ≤ 1 := hxs
    have hvolRk_lt : volume (𝓡 k) < ⊤ := by
      have : volume (𝓡 k) ≤ volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin k)) 1) :=
        measure_mono hRkball
      exact lt_of_le_of_lt this (measure_closedBall_lt_top)
    have hvolRk_ne : volume (𝓡 k) ≠ ⊤ := ne_of_lt hvolRk_lt
    have hvolbound : (volume (𝓡 k \ RkEps k ε)).toReal ≤ 2 * k * ε := by
      have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : (0 : ℕ) < k)
      have hkpe : ((k : ℝ) + 1) * ε < 1 := by
        have h2k : (0 : ℝ) < 2 * k := by positivity
        have hlt := (lt_div_iff₀ h2k).mp hε2
        have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (by omega : (1 : ℕ) ≤ k)
        nlinarith [hε, hkR, hlt, hk1]
      have hc0 : (0 : ℝ) ≤ 1 - ((k : ℝ) + 1) * ε := by linarith
      have hc1 : (1 : ℝ) - ((k : ℝ) + 1) * ε ≤ 1 := by nlinarith [hε, hkR]
      have hEpsRk : RkEps k ε ⊆ 𝓡 k := by
        rintro x ⟨hx1, hx2⟩
        exact EuclideanSpace.mem_scaledStdSimplex_iff.mpr
          ⟨fun i ↦ le_trans hε.le (hx1 i), by linarith⟩
      have hdiff : volume (𝓡 k \ RkEps k ε) = volume (𝓡 k) - volume (RkEps k ε) := by
        rw [measure_sdiff hEpsRk hmeasEps.nullMeasurableSet]
        exact ne_top_of_le_ne_top hvolRk_ne (measure_mono hEpsRk)
      have hscale := RkEps_volume k ε hc0
      set VR : ℝ := (volume (𝓡 k)).toReal with hVR
      have hVR0 : 0 ≤ VR := ENNReal.toReal_nonneg
      have hVReps : (volume (RkEps k ε)).toReal = (1 - ((k : ℝ) + 1) * ε) ^ k * VR := by
        rw [hscale, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), hVR]
      have hVReps_ne : volume (RkEps k ε) ≠ ⊤ := ne_top_of_le_ne_top hvolRk_ne (measure_mono hEpsRk)
      have hdiffR : (volume (𝓡 k \ RkEps k ε)).toReal = VR - (1 - ((k : ℝ) + 1) * ε) ^ k * VR := by
        rw [hdiff, ENNReal.toReal_sub_of_le (measure_mono hEpsRk) hvolRk_ne, hVR, ← hVReps]
      rw [hdiffR]
      have hbern : (1 : ℝ) - (k : ℝ) * (((k : ℝ) + 1) * ε) ≤ (1 - ((k : ℝ) + 1) * ε) ^ k := by
        have := one_add_mul_le_pow (a := -(((k : ℝ) + 1) * ε)) (by nlinarith [hc0]) k
        simpa [mul_comm, mul_neg, sub_eq_add_neg] using this
      have hstep1 : VR - (1 - ((k : ℝ) + 1) * ε) ^ k * VR ≤
          (k : ℝ) * (((k : ℝ) + 1) * ε) * VR := by nlinarith [hbern, hVR0]
      have hVRle : VR ≤ 1 / (k ! : ℝ) := R_volume_le k
      have hfacpos : (0 : ℝ) < (k ! : ℝ) := by exact_mod_cast Nat.factorial_pos k
      have hcoeff0 : (0 : ℝ) ≤ (k : ℝ) * (((k : ℝ) + 1) * ε) := by positivity
      have hstep2 : (k : ℝ) * (((k : ℝ) + 1) * ε) * VR ≤
          (k : ℝ) * (((k : ℝ) + 1) * ε) * (1 / (k ! : ℝ)) :=
        mul_le_mul_of_nonneg_left hVRle hcoeff0
      have harith : (k : ℝ) * ((k : ℝ) + 1) / (k ! : ℝ) ≤ 2 * k :=
        factorial_arith_bound k hk
      have hstep3 : (k : ℝ) * (((k : ℝ) + 1) * ε) * (1 / (k ! : ℝ)) ≤ 2 * k * ε := by
        have hrewrite : (k : ℝ) * (((k : ℝ) + 1) * ε) * (1 / (k ! : ℝ)) =
            ((k : ℝ) * ((k : ℝ) + 1) / (k ! : ℝ)) * ε := by ring
        rw [hrewrite]
        have := mul_le_mul_of_nonneg_right harith hε.le
        linarith [this]
      linarith [hstep1, hstep2, hstep3]
    classical
    intro G M hG hM hGM
    have hcont_f : Continuous (fun t : EuclideanSpace ℝ (Fin k) ↦ f t) := f.contMDiff.continuous
    set h := fun t ↦ (G t - G t * f t) ^ 2 with hh
    have hMsq : (0 : ℝ) ≤ M ^ 2 := sq_nonneg M
    have hfin : IsFiniteMeasure (volume.restrict (𝓡 k)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact hvolRk_lt⟩
    have hconstInt : IntegrableOn (fun _ : EuclideanSpace ℝ (Fin k) ↦ M ^ 2) (𝓡 k) volume :=
      integrable_const _
    have hbound : ∀ t ∈ 𝓡 k, h t ≤ M ^ 2 := by
      intro t ht
      have hft := hfIcc t
      obtain ⟨hf0', hf1'⟩ := hft
      have hGt : |G t| ≤ M := hGM t ht
      have heq : h t = (G t) ^ 2 * (1 - f t) ^ 2 := by
        change (G t - G t * f t) ^ 2 = (G t) ^ 2 * (1 - f t) ^ 2; ring
      rw [heq]
      have h1 : (G t) ^ 2 ≤ M ^ 2 := by
        have : |G t| ^ 2 ≤ M ^ 2 := by nlinarith [abs_nonneg (G t), hGt]
        rwa [sq_abs] at this
      have h2 : (1 - f t) ^ 2 ≤ 1 := by nlinarith [hf0', hf1']
      nlinarith [sq_nonneg (G t), sq_nonneg (1 - f t), h1, h2, hMsq]
    have hzero : ∀ t ∈ RkEps k ε, h t = 0 := by
      intro t ht
      have hft1 : f t = 1 := hf1.self_of_nhdsSet t ht
      change (G t - G t * f t) ^ 2 = 0
      rw [hft1]; ring
    have hnonneg : ∀ t, 0 ≤ h t := fun t ↦ sq_nonneg _
    have hmeas_h : Measurable h := by
      change Measurable (fun t ↦ (G t - G t * f t) ^ 2)
      exact ((hG.sub (hG.mul hcont_f.measurable)).pow_const 2)
    have hint : IntegrableOn h (𝓡 k) volume := by
      refine Integrable.mono' (g := fun _ ↦ M ^ 2) hconstInt ?_ ?_
      · exact hmeas_h.aestronglyMeasurable.restrict
      · filter_upwards [ae_restrict_mem hmeasRk] with t ht
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg t)]
        exact hbound t ht
    have hA : (∫ t in 𝓡 k, h t) ≤ M ^ 2 * (volume (𝓡 k \ RkEps k ε)).toReal := by
      have hle : ∀ t ∈ 𝓡 k, h t ≤ (𝓡 k \ RkEps k ε).indicator (fun _ ↦ M ^ 2) t := by
        intro t ht
        by_cases htE : t ∈ RkEps k ε
        · rw [hzero t htE, Set.indicator_apply]
          split_ifs
          · exact hMsq
          · exact le_refl 0
        · have hmem : t ∈ 𝓡 k \ RkEps k ε := ⟨ht, htE⟩
          rw [Set.indicator_apply, if_pos hmem]
          exact hbound t ht
      have hintind : IntegrableOn (fun t ↦ (𝓡 k \ RkEps k ε).indicator (fun _ ↦ M ^ 2) t)
          (𝓡 k) volume := by
        refine Integrable.mono' (g := fun _ ↦ M ^ 2) hconstInt ?_ ?_
        · exact (measurable_const.indicator (hmeasRk.diff hmeasEps)).aestronglyMeasurable.restrict
        · filter_upwards with t
          rw [Real.norm_eq_abs, Set.indicator_apply]
          split_ifs
          · rw [abs_of_nonneg hMsq]
          · simp [hMsq]
      have hmono := setIntegral_mono_on hint hintind hmeasRk hle
      refine hmono.trans_eq ?_
      rw [setIntegral_indicator (hmeasRk.diff hmeasEps),
        Set.inter_eq_self_of_subset_right Set.sdiff_subset,
        setIntegral_const, smul_eq_mul, mul_comm, Measure.real]
    exact ⟨hA, by nlinarith [hvolbound, hMsq]⟩

end PrimeGaps

open scoped ENNReal

namespace MeasureTheory

/-- For a real function in `L²`, the `L²` seminorm equals `ofReal` of the square root of the
integral of its square.
-/
theorem eLpNorm_two_eq_ofReal_sqrt_integral_sq
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {h : α → ℝ} (hmeas : AEStronglyMeasurable h μ) (hmem : MemLp h 2 μ) :
    eLpNorm h 2 μ = ENNReal.ofReal (√(∫ x, (h x) ^ 2 ∂μ)) := by
  have hint : Integrable (fun x ↦ (h x) ^ 2) μ :=
    (memLp_two_iff_integrable_sq hmeas).1 hmem
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2t : (2 : ℝ≥0∞).toReal = (2 : ℝ) := by norm_num
  rw [h2t]
  have henorm : ∀ x, ‖h x‖ₑ ^ (2 : ℝ) = ENNReal.ofReal ((h x) ^ 2) := by
    intro x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, ENNReal.rpow_natCast,
        Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have hlint : ∫⁻ x, ‖h x‖ₑ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (∫ x, (h x) ^ 2 ∂μ) := by
    rw [ofReal_integral_eq_lintegral_ofReal hint
        (Filter.Eventually.of_forall (fun x ↦ sq_nonneg _))]
    exact lintegral_congr (fun x ↦ henorm x)
  rw [hlint, Real.sqrt_eq_rpow,
      ENNReal.ofReal_rpow_of_nonneg (integral_nonneg (fun x ↦ sq_nonneg _))
        (by norm_num : (0 : ℝ) ≤ 1 / 2)]

end MeasureTheory

namespace PrimeGaps

/-- `L²`-approximation of bounded `L²` functions on the simplex `R_k` by smooth functions with
support contained in `R_k`.
-/
@[pg_tag "bg246" "lem_L2_density_smooth_Rk"]
theorem smooth_L2_approx_on_simplex (k : ℕ) (hk : 2 ≤ k) (F₀ : EuclideanSpace ℝ (Fin k) → ℝ)
    (hF₀mem : MemLp F₀ 2 (volume.restrict (𝓡 k)))
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ F₁ : EuclideanSpace ℝ (Fin k) → ℝ, ContDiff ℝ (⊤ : ℕ∞) F₁ ∧ tsupport F₁ ⊆ 𝓡 k ∧
      (eLpNorm (fun x ↦ F₀ x - F₁ x) 2 (volume.restrict (𝓡 k))).toReal < δ := by
  classical
  set μ : Measure (EuclideanSpace ℝ (Fin k)) := volume.restrict (𝓡 k) with hμ
  have hRkvol : volume (𝓡 k) < ∞ :=
    (EuclideanSpace.isCompact_scaledStdSimplex (k := k) (s := 1)).measure_lt_top
  have hμfin : IsFiniteMeasure μ := by
    rw [hμ]; exact ⟨by rw [Measure.restrict_apply_univ]; exact hRkvol⟩
  have hμfoc : IsFiniteMeasureOnCompacts μ := by infer_instance
  obtain ⟨g, hg_supp, hg_smooth, hg_close⟩ :=
    hF₀mem.exist_eLpNorm_sub_le (p := 2) (by norm_num) (by norm_num)
      (ε := δ / 3) (by positivity)
  have hg_cont : Continuous g := hg_smooth.continuous
  obtain ⟨C, hC⟩ :=
    (EuclideanSpace.isCompact_scaledStdSimplex (k := k) (s := 1)).exists_bound_of_continuousOn
      hg_cont.continuousOn
  set M : ℝ := max C 0 with hM
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMbd : ∀ t ∈ 𝓡 k, |g t| ≤ M := by
    intro t ht
    calc |g t| = ‖g t‖ := (Real.norm_eq_abs _).symm
      _ ≤ C := hC t ht
      _ ≤ M := le_max_left _ _
  have hkpos : (0 : ℝ) < k := by
    have : (2 : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  set ε_cut : ℝ := min (1 / (4 * k)) (((δ / (3 * (M + 1))) ^ 2) / (2 * k)) with hεcut
  have hεpos : 0 < ε_cut := lt_min (by positivity) (by positivity)
  have hεlt : ε_cut < 1 / (2 * k) :=
    calc ε_cut ≤ 1 / (4 * k) := min_le_left _ _
      _ < 1 / (2 * k) := one_div_lt_one_div_of_lt (by positivity) (by linarith)
  obtain ⟨χ, hχ_smooth, _, _, hχ_zero, hχ_bound⟩ :=
    exists_smooth_simplex_cutoff k hk ε_cut hεpos hεlt
  have hnum : 2 * k * ε_cut ≤ (δ / (3 * (M + 1))) ^ 2 := by
    have h2 : ε_cut ≤ ((δ / (3 * (M + 1))) ^ 2) / (2 * k) := min_le_right _ _
    have h2k : (0 : ℝ) < 2 * k := by positivity
    have h3 : ε_cut * (2 * k) ≤ (δ / (3 * (M + 1))) ^ 2 := by
      rw [le_div_iff₀ h2k] at h2; linarith
    nlinarith [h3]
  refine ⟨fun x ↦ g x * χ x, ?_, ?_, ?_⟩
  · exact hg_smooth.mul hχ_smooth
  · have hsupp_sub : Function.support (fun x ↦ g x * χ x) ⊆ 𝓡 k := by
      intro x hx
      simp only [Function.mem_support] at hx
      by_contra hxRk
      exact hx (by rw [hχ_zero x hxRk, mul_zero])
    calc tsupport (fun x ↦ g x * χ x) = closure (Function.support (fun x ↦ g x * χ x)) := rfl
      _ ⊆ closure (𝓡 k) := closure_mono hsupp_sub
      _ = 𝓡 k := (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).closure_eq
  · have hg_meas : Measurable g := hg_cont.measurable
    have hχ_cont : Continuous χ := hχ_smooth.continuous
    have hχ_meas : Measurable χ := hχ_cont.measurable
    have hF₀aesm : AEStronglyMeasurable F₀ μ := hF₀mem.aestronglyMeasurable
    have hgaesm : AEStronglyMeasurable g μ := hg_cont.aestronglyMeasurable
    have hχaesm : AEStronglyMeasurable χ μ := hχ_cont.aestronglyMeasurable
    set e : EuclideanSpace ℝ (Fin k) → ℝ := fun x ↦ g x * (1 - χ x) with he
    have heaesm : AEStronglyMeasurable e μ := by
      rw [he]
      exact (hg_meas.mul (measurable_const.sub hχ_meas)).aestronglyMeasurable
    have hS1 : eLpNorm (fun x ↦ F₀ x - g x * χ x) 2 μ ≤
          eLpNorm (fun x ↦ F₀ x - g x) 2 μ + eLpNorm e 2 μ := by
      have hcongr : (fun x ↦ F₀ x - g x * χ x) = (fun x ↦ (F₀ x - g x) + e x) := by
        funext x; rw [he]; ring
      rw [hcongr]
      exact eLpNorm_add_le (hF₀aesm.sub hgaesm) heaesm (by norm_num)
    have hS3 : eLpNorm e 2 μ ≤ ENNReal.ofReal (δ / 3) := by
      have he_cont : Continuous e := by
        rw [he]; exact hg_cont.mul (continuous_const.sub hχ_cont)
      have he_csupp : HasCompactSupport e := by
        rw [he]; exact hg_supp.mul_right
      have hemem : MemLp e 2 μ := he_cont.memLp_of_hasCompactSupport he_csupp
      have heq : eLpNorm e 2 μ = ENNReal.ofReal (√(∫ x, (e x) ^ 2 ∂μ)) :=
        eLpNorm_two_eq_ofReal_sqrt_integral_sq heaesm hemem
      rw [heq]
      have hint_eq : (∫ x, (e x) ^ 2 ∂μ) = ∫ x in 𝓡 k, (g x - g x * χ x) ^ 2 := by
        rw [hμ]
        apply setIntegral_congr_fun
          (EuclideanSpace.isClosed_scaledStdSimplex (k := k) (s := 1)).measurableSet
        intro x _
        rw [he]; ring
      obtain ⟨hb1, hb2⟩ := hχ_bound g M hg_meas hM0 hMbd
      have hint_bound : (∫ x, (e x) ^ 2 ∂μ) ≤ M ^ 2 * (2 * (k : ℝ) * ε_cut) := by
        rw [hint_eq]; exact hb1.trans hb2
      have hint_bound2 : (∫ x, (e x) ^ 2 ∂μ) ≤ M ^ 2 * (δ / (3 * (M + 1))) ^ 2 :=
        hint_bound.trans (mul_le_mul_of_nonneg_left hnum (by positivity))
      have hMfrac : M * (δ / (3 * (M + 1))) ≤ δ / 3 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [hM0, hδ.le]
      have hsqrt_le : √(∫ x, (e x) ^ 2 ∂μ) ≤ δ / 3 := by
        have hb : (∫ x, (e x) ^ 2 ∂μ) ≤ (M * (δ / (3 * (M + 1)))) ^ 2 := by
          rw [mul_pow]; exact hint_bound2
        calc √(∫ x, (e x) ^ 2 ∂μ)
            ≤ √((M * (δ / (3 * (M + 1)))) ^ 2) := Real.sqrt_le_sqrt hb
          _ = M * (δ / (3 * (M + 1))) := Real.sqrt_sq (by positivity)
          _ ≤ δ / 3 := hMfrac
      exact ENNReal.ofReal_le_ofReal hsqrt_le
    have hle : eLpNorm (fun x ↦ F₀ x - g x * χ x) 2 μ ≤ ENNReal.ofReal (2 * δ / 3) :=
      calc eLpNorm (fun x ↦ F₀ x - g x * χ x) 2 μ
          ≤ eLpNorm (fun x ↦ F₀ x - g x) 2 μ + eLpNorm e 2 μ := hS1
        _ ≤ ENNReal.ofReal (δ / 3) + ENNReal.ofReal (δ / 3) := add_le_add hg_close hS3
        _ = ENNReal.ofReal (2 * δ / 3) := by
            rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; ring_nf
    calc (eLpNorm (fun x ↦ F₀ x - g x * χ x) 2 μ).toReal ≤ (ENNReal.ofReal (2 * δ / 3)).toReal :=
            ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      _ = 2 * δ / 3 := ENNReal.toReal_ofReal (by positivity)
      _ < δ := by linarith

end PrimeGaps
