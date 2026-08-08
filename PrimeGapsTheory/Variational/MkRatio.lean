/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Variational.M105
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Bounds for the variational constant

Bounds each marginal quadratic form by the norm quadratic form and deduces bounds for `M k`.

## Main results

* `J_le_I`: Bounds a marginal quadratic form by the norm quadratic form.
* `M_le_k`: Shows that `M k ≤ k`.
* `M_pos`: Shows that `M (n + 1)` is positive.
-/

@[expose] public section

open MeasureTheory EuclideanSpace
open scoped PrimeGaps ENNReal

namespace PrimeGaps
open PropM105

/-- The Lebesgue volume of `{t : ES(ℝ, 1) | t 0 ∈ Set.Icc 0 1}` equals one. -/
private theorem volume_ES1_Icc_zero_one :
    volume {t : EuclideanSpace ℝ (Fin 1) | t 0 ∈ Set.Icc (0 : ℝ) 1} = 1 := by
  set S : Set (EuclideanSpace ℝ (Fin 1)) := {t | t 0 ∈ Set.Icc (0 : ℝ) 1}
  have hpre : (WithLp.toLp 2 (V := (Fin 1 → ℝ))) ⁻¹' S =
      {v : Fin 1 → ℝ | v 0 ∈ Set.Icc (0 : ℝ) 1} := by
    ext v; rfl
  have hvol1 : volume S = volume {v : Fin 1 → ℝ | v 0 ∈ Set.Icc (0 : ℝ) 1} := by
    have hmp := PiLp.volume_preserving_toLp (ι := Fin 1)
    have hmeas : MeasurableSet S :=
      measurableSet_Icc.preimage ((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous).measurable
    rw [← hpre]
    exact (hmp.measure_preimage hmeas.nullMeasurableSet).symm
  have hpre2 : (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' Set.Icc (0 : ℝ) 1 =
      {v : Fin 1 → ℝ | v 0 ∈ Set.Icc (0 : ℝ) 1} := by
    ext v
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rfl
  have hvol2 : volume {v : Fin 1 → ℝ | v 0 ∈ Set.Icc (0 : ℝ) 1} = volume (Set.Icc (0 : ℝ) 1) := by
    have hmp := volume_preserving_funUnique (Fin 1) ℝ
    rw [← hpre2]
    exact hmp.measure_preimage measurableSet_Icc.nullMeasurableSet
  rw [hvol1, hvol2, Real.volume_Icc]
  simp

/-- For every `y : ES(ℝ, n)`, the fibre of `finIsolateEquivProd ℝ m '' (𝓡 (n+1))`
over `y` is contained in `{t : ES(ℝ, 1) | t 0 ∈ Icc 0 1}`. -/
private theorem fibre_R_subset_Icc (n : ℕ) (m : Fin (n + 1)) (y : EuclideanSpace ℝ (Fin n)) :
    {t : EuclideanSpace ℝ (Fin 1) | (y, t) ∈ finIsolateEquivProd ℝ m '' (𝓡 (n + 1))}
      ⊆ {t : EuclideanSpace ℝ (Fin 1) | t 0 ∈ Set.Icc (0 : ℝ) 1} := by
  intro t ht
  simp only [Set.mem_ofPred_eq] at ht ⊢
  rw [mem_image_R_iff (k := n + 1) m (y, t), symm_finIsolate_apply,
      EuclideanSpace.mem_scaledStdSimplex_iff] at ht
  obtain ⟨hnn, hsum⟩ := ht
  have h0 : (0 : ℝ) ≤ t 0 := by simpa only [Fin.insertNth_apply_same] using hnn m
  have h1 : t 0 ≤ 1 := by
    rw [insertNth_sum n m (t 0) (fun j ↦ y j)] at hsum
    have hy_nn : ∀ j, (0 : ℝ) ≤ y j := fun j ↦ by
      simpa only [Fin.insertNth_apply_succAbove] using hnn (m.succAbove j)
    have : (0 : ℝ) ≤ ∑ j, y j := Finset.sum_nonneg (fun j _ ↦ hy_nn j)
    linarith
  exact ⟨h0, h1⟩

/-- `essSupSnd (finIsolateEquivProd m '' 𝓡 (n + 1)) ≤ 1`. -/
private theorem essSupSnd_R_le_one (n : ℕ) (m : Fin (n + 1)) :
    essSupSnd (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) volume volume ≤ 1 := by
  refine essSup_le_of_ae_le _ (Filter.Eventually.of_forall (fun y ↦ ?_))
  calc volume {t : EuclideanSpace ℝ (Fin 1) | (y, t) ∈ finIsolateEquivProd ℝ m '' (𝓡 (n + 1))}
      ≤ volume {t : EuclideanSpace ℝ (Fin 1) | t 0 ∈ Set.Icc (0 : ℝ) 1} :=
        measure_mono (fibre_R_subset_Icc n m y)
    _ = 1 := volume_ES1_Icc_zero_one

/-- `‖Vclm (n + 1) m f‖ ≤ ‖f‖` for every `f`. -/
private theorem norm_Vclm_apply_le (n : ℕ) (m : Fin (n + 1))
    (f : Lp ℝ 2 (volume.restrict (𝓡 (n + 1)))) :
    ‖Vclm (n + 1) m f‖ ≤ ‖f‖ := by
  have hf : MeasurePreserving (finIsolateEquivProd ℝ m).symm
      (volume.restrict (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))))
      (volume.restrict (𝓡 (n + 1))) := by
    have h := (measurePreserving_symm_finIsolateEquivProd m).restrict_preimage
      (isClosed_scaledStdSimplex (k := n + 1) (s := 1)).measurableSet
    rwa [← (finIsolateEquivProd ℝ m).image_eq_preimage_symm] at h
  have himg : MeasurableSet (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) :=
    (finIsolateEquivProd ℝ m).toHomeomorph.measurableEmbedding.measurableSet_image.mpr
      isClosed_scaledStdSimplex.measurableSet
  have hS : EssFiniteSnd (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) volume volume :=
    .of_isCompact isCompact_scaledStdSimplex
  set g : Lp ℝ 2 (volume.restrict (finIsolateEquivProd ℝ m '' (𝓡 (n + 1)))) :=
    (Lp.compMeasurePreservingₗᵢ ℝ _ hf).toContinuousLinearMap f with hgdef
  have hg_norm : ‖g‖ = ‖f‖ := by
    simp only [hgdef, LinearIsometry.coe_toContinuousLinearMap, LinearIsometry.norm_map]
  have hVclm : Vclm (n + 1) m f = Lp.integralLeftCLM himg hS g := rfl
  rw [hVclm]
  have hnorm_le : ‖Lp.integralLeftCLM himg hS g‖ ≤
      (essSupSnd (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) volume volume ^
          (2 : ℝ≥0∞)⁻¹.toReal).toReal * ‖g‖ :=
    Lp.norm_integralLeftCLM_le 2
  have hess := essSupSnd_R_le_one n m
  have hcoef : (essSupSnd (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) volume volume ^
        (2 : ℝ≥0∞)⁻¹.toReal).toReal ≤ 1 := by
    have hne : essSupSnd (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) volume volume ≠ ⊤ := hS
    have hexp_nn : (0 : ℝ) ≤ (2 : ℝ≥0∞)⁻¹.toReal := by simp
    have hrp_le : essSupSnd (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) volume volume ^
          (2 : ℝ≥0∞)⁻¹.toReal ≤ (1 : ℝ≥0∞) ^ (2 : ℝ≥0∞)⁻¹.toReal :=
      ENNReal.rpow_le_rpow hess hexp_nn
    rw [ENNReal.one_rpow] at hrp_le
    have hrp_ne : essSupSnd (finIsolateEquivProd ℝ m '' (𝓡 (n + 1))) volume volume ^
        (2 : ℝ≥0∞)⁻¹.toReal ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg hexp_nn hne
    have := (ENNReal.toReal_le_toReal hrp_ne (by simp)).mpr hrp_le
    simpa using this
  calc ‖Lp.integralLeftCLM himg hS g‖ ≤ _ * ‖g‖ := hnorm_le
    _ ≤ 1 * ‖g‖ := mul_le_mul_of_nonneg_right hcoef (norm_nonneg _)
    _ = ‖f‖ := by rw [one_mul, hg_norm]

/-- `J^{(m)}(f) ≤ I(f)` for every `f ∈ L²(𝓡_{n + 1})`. -/
theorem J_le_I (n : ℕ) (m : Fin (n + 1)) (f : Lp ℝ 2 (volume.restrict (𝓡 (n + 1)))) :
    PrimeGaps.J m f ≤ ‖f‖ ^ 2 := by
  rw [J_eq_normSq]
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_Vclm_apply_le n m f) 2

/-- `∑ₘ J^{(m)}(f) ≤ (n+1) · I(f)`. -/
theorem sum_J_le_k_I (n : ℕ) (f : Lp ℝ 2 (volume.restrict (𝓡 (n + 1)))) :
    ∑ m, PrimeGaps.J m f ≤ (n + 1 : ℝ) * ‖f‖ ^ 2 :=
  calc ∑ m, PrimeGaps.J m f ≤ ∑ _ : Fin (n + 1), ‖f‖ ^ 2 :=
        Finset.sum_le_sum (fun m _ ↦ J_le_I n m f)
    _ = (n + 1 : ℝ) * ‖f‖ ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]; ring

/-- The variational constant satisfies `M (n + 1) ≤ n + 1`. -/
theorem M_le_k (n : ℕ) : PrimeGaps.M (n + 1) ≤ (n + 1 : ℝ) := by
  apply Real.iSup_le _ (by positivity)
  intro f
  have hInn : 0 ≤ ‖f‖ ^ 2 := sq_nonneg _
  by_cases hf : ‖f‖ ^ 2 = 0
  · rw [hf, div_zero]; positivity
  · rw [div_le_iff₀ (lt_of_le_of_ne hInn (Ne.symm hf))]
    exact sum_J_le_k_I n f

/-- The Rayleigh family is bounded above (any `k`), by `∑ₘ ‖Vclm k m‖²`. -/
theorem M_bddAbove_gen (k : ℕ) : BddAbove (Set.range (fun f : Lp ℝ 2 (volume.restrict (𝓡 k)) ↦
      (∑ m, PrimeGaps.J m f) / ‖f‖ ^ 2)) := by
  refine ⟨∑ m : Fin k, ‖Vclm k m‖ ^ 2, ?_⟩
  rintro _ ⟨f, rfl⟩
  simp only
  have hInn : 0 ≤ ‖f‖ ^ 2 := sq_nonneg _
  by_cases hf : ‖f‖ ^ 2 = 0
  · rw [hf, div_zero]; positivity
  · rw [div_le_iff₀ (lt_of_le_of_ne hInn (Ne.symm hf))]
    calc ∑ m, PrimeGaps.J m f ≤ ∑ m : Fin k, ‖Vclm k m‖ ^ 2 * ‖f‖ ^ 2 :=
          Finset.sum_le_sum (fun m _ ↦ J_le_opNorm k m f)
      _ = (∑ m : Fin k, ‖Vclm k m‖ ^ 2) * ‖f‖ ^ 2 := by rw [Finset.sum_mul]

/-- The variational constant is nonnegative and its Rayleigh family is bounded above. -/
@[pg_tag "bg246" "lem_M_k_range"]
theorem M_k_range (k : ℕ) : 0 ≤ PrimeGaps.M k ∧
      BddAbove (Set.range (fun f : Lp ℝ 2 (volume.restrict (𝓡 k)) ↦
        (∑ m, PrimeGaps.J m f) / ‖f‖ ^ 2)) :=
  ⟨M_nonneg (k := k), M_bddAbove_gen k⟩

/-- The simplex `𝓡 (n + 1)` has positive volume. -/
theorem vol_R_pos (n : ℕ) : 0 < volume (𝓡 (n + 1)) := by
  set Rraw : Set (Fin (n + 1) → ℝ) :=
    {x | (∀ i, 0 ≤ x i) ∧ ∑ i, x i ≤ 1} with hRraw
  have hpre : (WithLp.toLp 2 (V := (Fin (n + 1) → ℝ))) ⁻¹' (𝓡 (n + 1)) = Rraw := by
    ext v
    rw [Set.mem_preimage, EuclideanSpace.mem_scaledStdSimplex_iff]
    rfl
  have hmeas : MeasurableSet (𝓡 (n + 1)) := isClosed_scaledStdSimplex.measurableSet
  have hvol : volume (𝓡 (n + 1)) = volume Rraw := by
    rw [← hpre]
    exact ((PiLp.volume_preserving_toLp (Fin (n + 1))).measure_preimage
      hmeas.nullMeasurableSet).symm
  rw [hvol]
  set U : Set (Fin (n + 1) → ℝ) := {x | (∀ i, 0 < x i) ∧ ∑ i, x i < 1} with hU
  have hUopen : IsOpen U := by
    have h1 : IsOpen {x : Fin (n + 1) → ℝ | ∀ i, 0 < x i} := by
      rw [Set.ofPred_forall]
      exact isOpen_iInter_of_finite (fun i ↦ isOpen_lt continuous_const (continuous_apply i))
    have h2 : IsOpen {x : Fin (n + 1) → ℝ | ∑ i, x i < 1} :=
      isOpen_lt (by fun_prop) continuous_const
    exact h1.inter h2
  have hUsub : U ⊆ Rraw := by
    intro x hx; exact ⟨fun i ↦ (hx.1 i).le, hx.2.le⟩
  have hUne : U.Nonempty := by
    refine ⟨fun _ ↦ (1 : ℝ) / (2 * (n + 1)), fun i ↦ by positivity, ?_⟩
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one_div,
      div_lt_one (by positivity)]
    push_cast; linarith
  exact lt_of_lt_of_le (hUopen.measure_pos volume hUne) (measure_mono hUsub)

/-- The variational constant `M (n + 1)` is positive. -/
theorem M_pos (n : ℕ) : 0 < PrimeGaps.M (n + 1) := by
  haveI : IsFiniteMeasure (volume.restrict (𝓡 (n + 1))) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact isCompact_scaledStdSimplex.measure_lt_top⟩
  have hmem1 : MemLp (fun _ : EuclideanSpace ℝ (Fin (n + 1)) ↦ (1 : ℝ)) 2
      (volume.restrict (𝓡 (n + 1))) := memLp_const 1
  set f₁ : Lp ℝ 2 (volume.restrict (𝓡 (n + 1))) := hmem1.toLp _ with hf₁
  have hI1 : ‖f₁‖ ^ 2 = volume.real (𝓡 (n + 1)) := by
    rw [hf₁, I_toLp_eq (n + 1) (fun _ ↦ (1 : ℝ)) hmem1]
    simp
  have hvne : volume (𝓡 (n + 1)) ≠ ⊤ := by
    rw [← Measure.restrict_apply_univ]; exact (measure_lt_top _ _).ne
  have hIpos : 0 < ‖f₁‖ ^ 2 := by
    rw [hI1]; exact ENNReal.toReal_pos (vol_R_pos n).ne' hvne
  set G : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun _ ↦ (1 : ℝ) with hGdef
  have hf₁_eq : hmem1.toLp _ = f₁ := rfl
  have hJeq0 : PrimeGaps.J (0 : Fin (n + 1)) f₁ = ∫ t in 𝓡 n,
          (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
              G (insertLp (0 : Fin (n + 1)) s t)) ^ 2 := by
    rw [← hf₁_eq]
    exact J_toLp_eq_iterated n 0 G hmem1
  have hJpos : 0 < PrimeGaps.J (0 : Fin (n + 1)) f₁ := by
    rw [hJeq0]
    have hmeas_reg : MeasurableSet (𝓡 n) := isClosed_scaledStdSimplex.measurableSet
    have hcompact_reg : IsCompact (𝓡 n) := isCompact_scaledStdSimplex
    have hInner : ∀ t ∈ 𝓡 n, (∫ s in Set.Icc (0 : ℝ) (1 - ∑ i, t i),
            G (insertLp (0 : Fin (n + 1)) s t)) ^ 2 = (1 - ∑ i, t i) ^ 2 := by
      intro t ht
      have htR : (∀ i, 0 ≤ t i) ∧ ∑ i, t i ≤ 1 := ht
      obtain ⟨_, hsum⟩ := htR
      have hle : (0 : ℝ) ≤ 1 - ∑ i, t i := by linarith
      simp only [hGdef, MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, Measure.real,
        Real.volume_Icc, sub_zero, ENNReal.toReal_ofReal hle]
    rw [setIntegral_congr_fun hmeas_reg hInner]
    have hcont : Continuous (fun t : EuclideanSpace ℝ (Fin n) ↦ (1 - ∑ i, t i) ^ 2) := by
      fun_prop
    have hint : IntegrableOn (fun t : EuclideanSpace ℝ (Fin n) ↦ (1 - ∑ i, t i) ^ 2) (𝓡 n) volume :=
      hcont.continuousOn.integrableOn_compact hcompact_reg
    set V : Set (EuclideanSpace ℝ (Fin n)) :=
      {t | (∀ i, 0 < t i) ∧ ∑ i, t i < 1 / 2} with hV
    have hVopen : IsOpen V := by
      have h1 : IsOpen {t : EuclideanSpace ℝ (Fin n) | ∀ i, 0 < t i} := by
        rw [Set.ofPred_forall]
        exact isOpen_iInter_of_finite
          (fun i ↦ isOpen_lt continuous_const (PiLp.continuous_apply 2 _ i))
      have h2 : IsOpen {t : EuclideanSpace ℝ (Fin n) | ∑ i, t i < 1 / 2} :=
        isOpen_lt (by fun_prop) continuous_const
      exact h1.inter h2
    have hVsub : V ⊆ 𝓡 n := fun t ht ↦ by
      exact ⟨fun i ↦ (ht.1 i).le, by linarith [ht.2]⟩
    have hVne : V.Nonempty := by
      refine ⟨WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ) / (4 * (n + 1))), fun i ↦ ?_, ?_⟩
      · change (0 : ℝ) < (1 : ℝ) / (4 * (n + 1))
        positivity
      · have hsum : ∑ i, (WithLp.toLp 2 (fun _ : Fin n ↦ (1 : ℝ) / (4 * (n + 1))) : _) i =
            ∑ i : Fin n, (1 : ℝ) / (4 * (n + 1)) :=
          Finset.sum_congr rfl (fun _ _ ↦ rfl)
        rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          mul_one_div, div_lt_iff₀ (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have hVfin : volume V < ⊤ := lt_of_le_of_lt (measure_mono hVsub) hcompact_reg.measure_lt_top
    have hVpos : 0 < volume.real V :=
      ENNReal.toReal_pos (hVopen.measure_pos volume hVne).ne' hVfin.ne
    have hlb : (1 / 4 : ℝ) * volume.real V ≤ ∫ t in V, (1 - ∑ i, t i) ^ 2 := by
      rw [mul_comm, ← smul_eq_mul, ← MeasureTheory.setIntegral_const (1 / 4 : ℝ)]
      refine setIntegral_mono_on (integrableOn_const hVfin.ne)
        (hint.mono_set hVsub) hVopen.measurableSet (fun t ht ↦ ?_)
      have : ∑ i, t i < 1 / 2 := ht.2
      nlinarith [sq_nonneg (1 - ∑ i, t i)]
    have hmono : ∫ t in V, (1 - ∑ i, t i) ^ 2 ≤ ∫ t in 𝓡 n, (1 - ∑ i, t i) ^ 2 :=
      setIntegral_mono_set hint (Filter.Eventually.of_forall (fun t ↦ sq_nonneg _))
        (Filter.Eventually.of_forall hVsub)
    have : (0 : ℝ) < (1 / 4 : ℝ) * volume.real V := by positivity
    linarith
  have hsumpos : 0 < ∑ m, PrimeGaps.J m f₁ :=
    Finset.sum_pos' (fun m _ ↦ by rw [J_eq_normSq]; positivity) ⟨0, Finset.mem_univ _, hJpos⟩
  have hle : (∑ m, PrimeGaps.J m f₁) / ‖f₁‖ ^ 2 ≤ PrimeGaps.M (n + 1) :=
    le_ciSup (M_bddAbove_gen (n + 1)) f₁
  have hrpos : 0 < (∑ m, PrimeGaps.J m f₁) / ‖f₁‖ ^ 2 := div_pos hsumpos hIpos
  exact lt_of_lt_of_le hrpos hle

/-- The variational constant `M k` is positive in every dimension `k ≠ 0`. -/
theorem M_pos_of_ne_zero {k : ℕ} (hk : k ≠ 0) : 0 < PrimeGaps.M k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk
  exact M_pos n

end PrimeGaps
