/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Integral.Prod


/-!
# Tonelli operators on Lᵖ

For `S ⊆ α × β` that is "essentially finite" along `β`, we define a continuous linear operator
`Lp.integralLeftCLM : Lᵖ(S) → Lᵖ(α)` given by `f ↦ (x ↦ ∫ y in S, f(x, y) ∂ν)`.
-/

@[expose] public section

open ENNReal MeasureTheory Measure

namespace MeasureTheory

variable {p : ℝ≥0∞} {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (S : Set (α × β)) (μ : Measure α) (ν : Measure β) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The essential supremum (along the first variable) of the `ν`-measure of the second-variable
fibres `{y | (x, y) ∈ S}` of a set `S`. -/
noncomputable def essSupSnd : ℝ≥0∞ := essSup (fun x ↦ ν {y | (x, y) ∈ S}) μ

/-- `S` has essentially bounded second-variable fibres: `essSupSnd S μ ν` is finite. -/
def EssFiniteSnd : Prop := essSupSnd S μ ν ≠ ⊤

variable {S μ ν}

/-- The essential supremum of the second-variable fibre measure is itself an essential upper
bound for that measure. -/
theorem ae_measure_le_essSupSnd : ∀ᵐ x ∂μ, ν {y | (x, y) ∈ S} ≤ essSupSnd S μ ν := ae_le_essSup

/-- Hölder bound on a single fibre: for `g` vanishing off a measurable set `T` and `1 ≤ r`, the
`r`-th power of `∫ g` is at most `ν T ^ (r - 1)` times `∫⁻ ‖g‖ₑ ^ r`. -/
private theorem enorm_integral_rpow_le_of_eqOn_zero {r : ℝ} (hr0 : 0 < r) (hr1 : 1 ≤ r)
    {T : Set β} (hT : MeasurableSet T) {g : β → E} (hg : AEStronglyMeasurable g ν)
    (hgT : ∀ y ∉ T, g y = 0) :
    ‖∫ y, g y ∂ν‖ₑ ^ r ≤ ν T ^ (r - 1) * ∫⁻ y, ‖g y‖ₑ ^ r ∂ν := by
  have hLHS (y : β) : (‖g y‖ₑ ^ r) ^ (1 / r) *
      (T.indicator (1 : β → ℝ≥0∞) y) ^ (1 - 1 / r) = ‖g y‖ₑ := by
    by_cases hy : y ∈ T
    · rw [Set.indicator_of_mem hy, Pi.one_apply, ENNReal.one_rpow, mul_one, ← ENNReal.rpow_mul,
        one_div, mul_inv_cancel₀ hr0.ne', ENNReal.rpow_one]
    · rw [hgT y hy, enorm_zero, ENNReal.zero_rpow_of_pos hr0,
        ENNReal.zero_rpow_of_pos (div_pos one_pos hr0), zero_mul]
  have h2 : ∫⁻ y, ‖g y‖ₑ ∂ν ≤ (∫⁻ y, ‖g y‖ₑ ^ r ∂ν) ^ (1 / r) * ν T ^ (1 - 1 / r) :=
    calc ∫⁻ y, ‖g y‖ₑ ∂ν
        = ∫⁻ y, (‖g y‖ₑ ^ r) ^ (1 / r) *
            (T.indicator (1 : β → ℝ≥0∞) y) ^ (1 - 1 / r) ∂ν := (lintegral_congr hLHS).symm
      _ ≤ (∫⁻ y, ‖g y‖ₑ ^ r ∂ν) ^ (1 / r) * (∫⁻ y, T.indicator (1 : β → ℝ≥0∞) y ∂ν) ^ (1 - 1 / r) :=
          lintegral_mul_norm_pow_le (hg.enorm.pow_const r)
            (measurable_const.indicator hT).aemeasurable (div_pos one_pos hr0).le
            (sub_nonneg.mpr ((div_le_one hr0).mpr hr1)) (by norm_num)
      _ = (∫⁻ y, ‖g y‖ₑ ^ r ∂ν) ^ (1 / r) * ν T ^ (1 - 1 / r) := by
          rw [lintegral_indicator_one hT]
  have hexp2 : 1 / r * r = 1 := by rw [one_div, inv_mul_cancel₀ hr0.ne']
  have hexp : (1 - 1 / r) * r = r - 1 := by rw [sub_mul, one_mul, one_div, inv_mul_cancel₀ hr0.ne']
  calc ‖∫ y, g y ∂ν‖ₑ ^ r
      ≤ ((∫⁻ y, ‖g y‖ₑ ^ r ∂ν) ^ (1 / r) * ν T ^ (1 - 1 / r)) ^ r :=
        ENNReal.rpow_le_rpow ((enorm_integral_le_lintegral_enorm _).trans h2) hr0.le
    _ = (∫⁻ y, ‖g y‖ₑ ^ r ∂ν) * ν T ^ (r - 1) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hr0.le, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul,
          hexp2, hexp, ENNReal.rpow_one]
    _ = ν T ^ (r - 1) * ∫⁻ y, ‖g y‖ₑ ^ r ∂ν := mul_comm _ _

/-- Quantitative bound underlying `memLp_integral_left`: partial integration along the second
variable maps `Lᵖ` into `Lᵖ` with operator norm at most `(essSupSnd S) ^ q`. -/
theorem eLpNorm_integral_left_le [SFinite ν] (q : ℝ≥0∞) [p.HolderConjugate q]
    (hMS : MeasurableSet S) (hS : EssFiniteSnd S μ ν)
    {f : α × β → E} (hf : MemLp (S.indicator f) p (μ.prod ν)) :
    eLpNorm (fun x ↦ ∫ y, S.indicator f (x, y) ∂ν) p μ ≤
      essSupSnd S μ ν ^ q⁻¹.toReal * eLpNorm (S.indicator f) p (μ.prod ν) := by
  set F := S.indicator f with hFdef
  have hub := ae_measure_le_essSupSnd (μ := μ) (ν := ν) (S := S)
  have hp : 1 ≤ p := HolderConjugate.one_le p q
  cases p with
  | top =>
    obtain rfl : q = 1 := (HolderConjugate.eq_top_iff_eq_one _ q).mp rfl
    rw [inv_one, toReal_one, rpow_one]
    simp only [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    have haeC : ∀ᵐ z ∂(μ.prod ν), ‖F z‖ₑ ≤ essSup (fun z ↦ ‖F z‖ₑ) (μ.prod ν) :=
      ENNReal.ae_le_essSup _
    refine essSup_le_of_ae_le _ ?_
    filter_upwards [hub, ae_ae_of_ae_prod haeC] with x hxub hxae
    have hSx : MeasurableSet {y | (x, y) ∈ S} := hMS.preimage measurable_prodMk_left
    calc ‖∫ y, F (x, y) ∂ν‖ₑ
        ≤ ∫⁻ y, ‖F (x, y)‖ₑ ∂ν := enorm_integral_le_lintegral_enorm _
      _ ≤ ∫⁻ y, {y | (x, y) ∈ S}.indicator
              (fun _ ↦ essSup (fun z ↦ ‖F z‖ₑ) (μ.prod ν)) y ∂ν := by
            apply lintegral_mono_ae
            filter_upwards [hxae] with y hy
            by_cases hymem : (x, y) ∈ S <;> aesop
      _ = essSup (fun z ↦ ‖F z‖ₑ) (μ.prod ν) * ν {y | (x, y) ∈ S} := by
            rw [lintegral_indicator hSx, setLIntegral_const]
      _ ≤ essSupSnd S μ ν * essSup (fun z ↦ ‖F z‖ₑ) (μ.prod ν) :=
            (mul_le_mul_right hxub _).trans (le_of_eq (mul_comm _ _))
  | coe p =>
    have hp0 : (p : ℝ≥0∞) ≠ 0 := (lt_of_lt_of_le zero_lt_one hp).ne'
    have hptop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hr1 : 1 ≤ (p : ℝ≥0∞).toReal := by simpa using ENNReal.toReal_mono hptop hp
    have hr0 : 0 < (p : ℝ≥0∞).toReal := by positivity
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop]
    set r := (p : ℝ≥0∞).toReal with hrdef
    rw [show (q : ℝ≥0∞)⁻¹.toReal = 1 - 1 / r by
      rw [hrdef, ← HolderConjugate.one_sub_inv (p : ℝ≥0∞) q,
        ENNReal.toReal_sub_of_le (ENNReal.inv_le_one.mpr hp) one_ne_top,
        ENNReal.toReal_inv, ENNReal.toReal_one, one_div]]
    have hpt : ∀ᵐ x ∂μ, ‖∫ y, F (x, y) ∂ν‖ₑ ^ r ≤
        essSupSnd S μ ν ^ (r - 1) * ∫⁻ y, ‖F (x, y)‖ₑ ^ r ∂ν := by
      filter_upwards [hub, hf.1.prodMk_left] with x hxub hxmeas
      refine (enorm_integral_rpow_le_of_eqOn_zero (T := {y | (x, y) ∈ S}) hr0 hr1
        (hMS.preimage measurable_prodMk_left) hxmeas
        fun y hy ↦ Set.indicator_of_notMem (s := S) (a := (x, y)) hy f).trans ?_
      gcongr
    have hbound : ∫⁻ x, ‖∫ y, F (x, y) ∂ν‖ₑ ^ r ∂μ ≤
        essSupSnd S μ ν ^ (r - 1) * ∫⁻ z, ‖F z‖ₑ ^ r ∂(μ.prod ν) :=
      calc ∫⁻ x, ‖∫ y, F (x, y) ∂ν‖ₑ ^ r ∂μ
          ≤ ∫⁻ x, essSupSnd S μ ν ^ (r - 1) * ∫⁻ y, ‖F (x, y)‖ₑ ^ r ∂ν ∂μ := lintegral_mono_ae hpt
        _ = essSupSnd S μ ν ^ (r - 1) * ∫⁻ x, ∫⁻ y, ‖F (x, y)‖ₑ ^ r ∂ν ∂μ :=
            lintegral_const_mul' _ _ (ENNReal.rpow_lt_top_of_nonneg (by positivity) hS).ne
        _ = essSupSnd S μ ν ^ (r - 1) * ∫⁻ z, ‖F z‖ₑ ^ r ∂(μ.prod ν) := by
            rw [← lintegral_prod _ (hf.1.enorm.pow_const r)]
    calc (∫⁻ x, ‖∫ y, F (x, y) ∂ν‖ₑ ^ r ∂μ) ^ (1 / r)
        ≤ (essSupSnd S μ ν ^ (r - 1) * ∫⁻ z, ‖F z‖ₑ ^ r ∂(μ.prod ν)) ^ (1 / r) :=
          ENNReal.rpow_le_rpow hbound (le_of_lt (div_pos one_pos hr0))
      _ = essSupSnd S μ ν ^ (1 - 1 / r) * (∫⁻ z, ‖F z‖ₑ ^ r ∂(μ.prod ν)) ^ (1 / r) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (div_pos one_pos hr0).le, ← ENNReal.rpow_mul,
            mul_one_div, sub_div, div_self hr0.ne']

theorem memLp_integral_left [SFinite ν]
    (hMS : MeasurableSet S) (hS : EssFiniteSnd S μ ν) (hp : 1 ≤ p)
    {f : α × β → E} (hf : MemLp f p ((μ.prod ν).restrict S)) :
    MemLp (fun x ↦ ∫ y, S.indicator f (x, y) ∂ν) p μ := by
  have := Fact.mk hp
  rw [← MeasureTheory.memLp_indicator_iff_restrict hMS] at hf
  refine ⟨hf.1.integral_prod_right',
    (eLpNorm_integral_left_le p.conjExponent hMS hS hf).trans_lt ?_⟩
  exact ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hS) hf.2

omit [NormedSpace ℝ E] in
/-- Almost every second-variable fibre of an `Lᵖ` (`1 ≤ p`) function on a product measure is
itself `Lᵖ`. -/
theorem memLp_prodMk_left [SFinite ν] (hp : 1 ≤ p) {F : α × β → E}
    (hF : MemLp F p (μ.prod ν)) : ∀ᵐ x ∂μ, MemLp (fun y ↦ F (x, y)) p ν := by
  cases p with
  | top =>
    have haeC : ∀ᵐ z ∂(μ.prod ν), ‖F z‖ₑ ≤ essSup (fun z ↦ ‖F z‖ₑ) (μ.prod ν) :=
      ENNReal.ae_le_essSup _
    have hC : essSup (fun z ↦ ‖F z‖ₑ) (μ.prod ν) < ⊤ := by exact_mod_cast hF.2
    filter_upwards [hF.1.prodMk_left, ae_ae_of_ae_prod haeC] with x hxm hxae
    refine ⟨hxm, ?_⟩
    rw [eLpNorm_exponent_top, eLpNormEssSup_eq_essSup_enorm]
    exact (essSup_le_of_ae_le _ hxae).trans_lt hC
  | coe p =>
    have hp0 : (p : ℝ≥0∞) ≠ 0 := (zero_lt_one.trans_le hp).ne'
    have hptop : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.coe_ne_top
    have hfin : ∫⁻ x, ∫⁻ y, ‖F (x, y)‖ₑ ^ (p : ℝ≥0∞).toReal ∂ν ∂μ < ⊤ := by
      rw [← lintegral_prod _ (hF.1.enorm.pow_const _)]
      exact lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop hF.2
    filter_upwards [hF.1.prodMk_left,
      ae_lt_top' (hF.1.enorm.pow_const _).lintegral_prod_right' hfin.ne] with x hxm hxfin
    exact ⟨hxm, (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hptop).mpr hxfin⟩

omit [NormedSpace ℝ E] in
/-- For a set with essentially bounded fibres, the fibres of an `Lᵖ` (`1 ≤ p`) function are
integrable along the second variable. -/
theorem integrable_indicator_prodMk_left [SFinite ν] (hS : EssFiniteSnd S μ ν) (hp : 1 ≤ p)
    {f : α × β → E} (hf : MemLp (S.indicator f) p (μ.prod ν)) :
    ∀ᵐ x ∂μ, Integrable (fun y ↦ S.indicator f (x, y)) ν := by
  filter_upwards [memLp_prodMk_left hp hf, ae_measure_le_essSupSnd (μ := μ) (ν := ν) (S := S)]
    with x hxfib hxub
  rw [← memLp_one_iff_integrable]
  refine hxfib.mono_exponent_of_measure_support_ne_top (s := {y | (x, y) ∈ S})
    (fun y hy ↦ ?_) (hxub.trans_lt (lt_top_iff_ne_top.mpr hS)).ne hp
  aesop

/-- Partial integration along the second variable, as a linear map on `Lᵖ` for a set with
essentially bounded fibres (`1 ≤ p`). -/
noncomputable def Lp.integralLeftₗ [SFinite ν] [Fact (1 ≤ p)]
    (hMS : MeasurableSet S) (hS : EssFiniteSnd S μ ν) :
    Lp E p ((μ.prod ν).restrict S) →ₗ[ℝ] Lp E p μ where
  toFun f := MemLp.toLp _ (memLp_integral_left hMS hS Fact.out (Lp.memLp f))
  map_add' f g := Lp.ext <| by
    have hp : 1 ≤ p := Fact.out
    have hfg : ∀ᵐ z ∂(μ.prod ν),
        S.indicator (⇑(f + g)) z = S.indicator (⇑f) z + S.indicator (⇑g) z := by
      filter_upwards [(ae_eq_restrict_iff_indicator_ae_eq hMS).mp (Lp.coeFn_add f g)] with z hz
      rw [hz]
      by_cases hzS : z ∈ S
      · simp [Set.indicator_of_mem hzS]
      · simp [Set.indicator_of_notMem hzS]
    filter_upwards [MemLp.coeFn_toLp (memLp_integral_left hMS hS hp (Lp.memLp (f + g))),
      Lp.coeFn_add (MemLp.toLp _ (memLp_integral_left hMS hS hp (Lp.memLp f)))
        (MemLp.toLp _ (memLp_integral_left hMS hS hp (Lp.memLp g))),
      MemLp.coeFn_toLp (memLp_integral_left hMS hS hp (Lp.memLp f)),
      MemLp.coeFn_toLp (memLp_integral_left hMS hS hp (Lp.memLp g)),
      ae_ae_of_ae_prod hfg,
      integrable_indicator_prodMk_left hS hp ((memLp_indicator_iff_restrict hMS).mpr (Lp.memLp f)),
      integrable_indicator_prodMk_left hS hp ((memLp_indicator_iff_restrict hMS).mpr (Lp.memLp g))]
      with x h1 h2 h3 h4 hz hIf hIg
    rw [h1, h2, Pi.add_apply, h3, h4, integral_congr_ae hz, integral_add hIf hIg]
  map_smul' c f := Lp.ext <| by
    have hp : 1 ≤ p := Fact.out
    have hcf : ∀ᵐ z ∂(μ.prod ν), S.indicator (⇑(c • f)) z = c • S.indicator (⇑f) z := by
      filter_upwards [(ae_eq_restrict_iff_indicator_ae_eq hMS).mp (Lp.coeFn_smul c f)] with z hz
      rw [hz]
      by_cases hzS : z ∈ S
      · simp [Set.indicator_of_mem hzS]
      · simp [Set.indicator_of_notMem hzS]
    filter_upwards [MemLp.coeFn_toLp (memLp_integral_left hMS hS hp (Lp.memLp (c • f))),
      Lp.coeFn_smul c (MemLp.toLp _ (memLp_integral_left hMS hS hp (Lp.memLp f))),
      MemLp.coeFn_toLp (memLp_integral_left hMS hS hp (Lp.memLp f)),
      ae_ae_of_ae_prod hcf]
      with x h1 h2 h3 hz
    rw [RingHom.id_apply, h1, h2, Pi.smul_apply, h3, integral_congr_ae hz, integral_smul]

theorem Lp.norm_integralLeftₗ_le [SFinite ν] [Fact (1 ≤ p)] (q : ℝ≥0∞) [p.HolderConjugate q]
    {hMS : MeasurableSet S} {hS : EssFiniteSnd S μ ν} {f : Lp E p ((μ.prod ν).restrict S)} :
    ‖Lp.integralLeftₗ hMS hS f‖ ≤ (essSupSnd S μ ν ^ q⁻¹.toReal).toReal * ‖f‖ := by
  have hp : 1 ≤ p := Fact.out
  have hFmem := (memLp_indicator_iff_restrict hMS).mpr (Lp.memLp f)
  have hRHS : essSupSnd S μ ν ^ q⁻¹.toReal * eLpNorm (S.indicator f) p (μ.prod ν) ≠ ⊤ :=
    (ENNReal.mul_lt_top (ENNReal.rpow_lt_top_of_nonneg (by positivity) hS) hFmem.2).ne
  change ‖MemLp.toLp _ (memLp_integral_left hMS hS hp (Lp.memLp f))‖ ≤
    (essSupSnd S μ ν ^ q⁻¹.toReal).toReal * ‖f‖
  rw [Lp.norm_def, Lp.norm_def,
    eLpNorm_congr_ae (MemLp.coeFn_toLp (memLp_integral_left hMS hS hp (Lp.memLp f))),
    ← eLpNorm_indicator_eq_eLpNorm_restrict hMS, ← ENNReal.toReal_mul]
  exact ENNReal.toReal_mono hRHS (eLpNorm_integral_left_le q hMS hS hFmem)

/-- Partial integration along the second variable, as a continuous linear map on `Lᵖ` for a set
with essentially bounded fibres (`1 ≤ p`); its operator norm is at most
`(essSupSnd S) ^ (1 - 1/p)`. -/
noncomputable def Lp.integralLeftCLM [SFinite ν] [Fact (1 ≤ p)]
    (hMS : MeasurableSet S) (hS : EssFiniteSnd S μ ν) :
    Lp E p ((μ.prod ν).restrict S) →L[ℝ] Lp E p μ :=
  (Lp.integralLeftₗ hMS hS).mkContinuous (essSupSnd S μ ν ^ p.conjExponent⁻¹.toReal).toReal fun _ ↦
    norm_integralLeftₗ_le _

theorem Lp.norm_integralLeftCLM_le [SFinite ν] [Fact (1 ≤ p)] (q : ℝ≥0∞) [p.HolderConjugate q]
    {hMS : MeasurableSet S} {hS : EssFiniteSnd S μ ν} {f : Lp E p ((μ.prod ν).restrict S)} :
    ‖Lp.integralLeftCLM hMS hS f‖ ≤ (essSupSnd S μ ν ^ q⁻¹.toReal).toReal * ‖f‖ :=
  norm_integralLeftₗ_le (hMS := hMS) (hS := hS) q

end MeasureTheory
