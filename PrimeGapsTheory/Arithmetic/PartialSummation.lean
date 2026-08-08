/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.HAsymptotic
import PrimeGapsTheory.Tactic.PaperTag

/-!
# Partial summation for a sieve sum

A partial-summation estimate for a weighted sieve sum.

## Main definitions

* `Gmax`: The maximum of the weighted summatory function.

## Main results

* `abel_identity`: Abel’s partial-summation identity.
* `lem_partial_sum`: The partial-summation estimate for the sieve sum.
-/

@[expose] public section

open scoped Finset Interval

namespace PrimeGaps

/-- `Gmax G := sup_{t∈[0,1]} (|G t| + |G'(t)|)`. -/
noncomputable def Gmax (G : ℝ → ℝ) : ℝ := ⨆ t : ↥(Set.Icc (0 : ℝ) 1), (|G t| + |deriv G t|)

private lemma SieveDatum.h_zero (S : SieveDatum) : S.h 0 = 0 := by simp [SieveDatum.h]

private lemma le_of_mem_uIcc {a b t : ℝ} (hab : a ≤ b) (ht : t ∈ [[a, b]]) : a ≤ t :=
  (Set.uIcc_of_le hab ▸ ht).1

private lemma continuousOn_log_uIcc {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn Real.log ([[a, b]]) :=
  Real.continuousOn_log.mono fun t ht ↦ by
    simpa using (lt_of_lt_of_le ha (le_of_mem_uIcc hab ht)).ne'

private lemma natCast_ne_of_floor_ne {z : ℝ} (hzInt : ¬((⌊z⌋₊ : ℝ) = z)) (n : ℕ) : (n : ℝ) ≠ z :=
  fun hn ↦ hzInt <| by rw [← hn, Nat.floor_natCast]

/-- `|G t| ≤ Gmax G` and `|deriv G t| ≤ Gmax G` for `t ∈ [0, 1]` and `G` of class `C¹`. -/
theorem Gmax_bounds (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |G t| ≤ Gmax G ∧ |deriv G t| ≤ Gmax G := by
  have hGc : Continuous G := hG.continuous
  have hG'c : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hcont : Continuous (fun s : ↥(Set.Icc (0 : ℝ) 1) ↦ |G ↑s| + |deriv G ↑s|) := by fun_prop
  have hcompact : CompactSpace (↥(Set.Icc (0 : ℝ) 1)) := isCompact_iff_compactSpace.mp isCompact_Icc
  have hle : |G t| + |deriv G t| ≤ Gmax G := by
    simpa [Gmax] using le_ciSup (isCompact_range hcont).bddAbove ⟨t, ht⟩
  exact ⟨(le_add_of_nonneg_right (abs_nonneg _)).trans hle,
    (le_add_of_nonneg_left (abs_nonneg _)).trans hle⟩

private lemma Gmax_nonneg (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) : 0 ≤ Gmax G :=
  (abs_nonneg (G 0)).trans (Gmax_bounds G hG (by norm_num)).1

/-- `S.H t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, S.h k` at every `t ≥ 0` that is not a natural number. -/
theorem H_ae_summatory (S : SieveDatum) (t : ℝ) (ht : 0 ≤ t) (htn : ∀ n : ℕ, (n : ℝ) ≠ t) :
    S.H t = ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, S.h k := by
  unfold SieveDatum.H
  have hfloor_lt : (⌊t⌋₊ : ℝ) < t := lt_of_le_of_ne (Nat.floor_le ht) (htn ⌊t⌋₊)
  apply Finset.sum_subset
  · intro d hd
    rw [Finset.mem_filter, Finset.mem_range] at hd
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hd.2.2.le⟩
  · intro d hd hdni
    rw [Finset.mem_Icc] at hd
    rw [Finset.mem_filter, Finset.mem_range] at hdni
    push Not at hdni
    rcases Nat.eq_zero_or_pos d with hd0 | hdpos
    · rw [hd0]; exact S.h_zero
    · have hdt : (d : ℝ) < t := lt_of_le_of_lt (by exact_mod_cast hd.2) hfloor_lt
      exact absurd (hdni (Nat.lt_ceil.mpr hdt) hdpos) (not_le.mpr hdt)

/-- The summatory function `S.H` is monotone, being a partial sum of the nonnegative weights
`S.h` over an index set that grows with the argument. -/
private theorem H_monotone (S : SieveDatum) : Monotone S.H := by
  intro x y hxy
  unfold SieveDatum.H
  have hsubset : (Finset.range ⌈x⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < x)
        ⊆ (Finset.range ⌈y⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < y) := by
    intro d hd
    rw [Finset.mem_filter, Finset.mem_range] at hd ⊢
    obtain ⟨hdr, hdpos, hdx⟩ := hd
    exact ⟨lt_of_lt_of_le hdr (Nat.ceil_le_ceil hxy), hdpos, lt_of_lt_of_le hdx hxy⟩
  exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (fun d _ _ ↦ S.h_nonneg d)

/-- The Abel kernel `t ↦ f (log t / L) / (t * L)` is continuous on `[1, z]`, for any continuous `f`
and any `L > 0`: `log` is continuous away from `0`, and `t * L` is nonzero throughout. -/
private lemma continuousOn_comp_log_div_mul {f : ℝ → ℝ} (hf : Continuous f) {L z : ℝ}
    (hLpos : 0 < L) (hz1 : (1 : ℝ) ≤ z) :
    ContinuousOn (fun t ↦ f (Real.log t / L) / (t * L)) ([[1, z]]) := by
  refine ContinuousOn.div (hf.comp_continuousOn ((continuousOn_log_uIcc one_pos hz1).div_const L))
    (continuous_id.mul continuous_const).continuousOn fun t ht ↦ ?_
  exact (mul_pos (by linarith [le_of_mem_uIcc hz1 ht]) hLpos).ne'

/-- `t ↦ c * log t` is interval integrable on `[1, z]`, `log` being continuous away from `0`. -/
lemma intervalIntegrable_const_mul_log (c : ℝ) {z : ℝ} (hz1 : (1 : ℝ) ≤ z) :
    IntervalIntegrable (fun t ↦ c * Real.log t) MeasureTheory.volume 1 z :=
  (continuousOn_const.mul (continuousOn_log_uIcc one_pos hz1)).intervalIntegrable

/-- The summatory function `S.H` is interval integrable on `[1, z]`, being monotone there. -/
lemma intervalIntegrable_H (S : SieveDatum) {z : ℝ} (hz1 : (1 : ℝ) ≤ z) :
    IntervalIntegrable S.H MeasureTheory.volume 1 z := by
  apply MonotoneOn.intervalIntegrable
  rw [Set.uIcc_of_le hz1]
  exact (H_monotone S).monotoneOn _

/-- Interval integrability on `[1, z]` survives taking the absolute value and dividing by `t`,
since `1 / t` is continuous there. -/
private lemma intervalIntegrable_abs_div_self {ρ : ℝ → ℝ} {z : ℝ} (hz1 : (1 : ℝ) ≤ z)
    (hρ : IntervalIntegrable ρ MeasureTheory.volume 1 z) :
    IntervalIntegrable (fun t ↦ |ρ t| / t) MeasureTheory.volume 1 z := by
  have hinvt : ContinuousOn (fun t : ℝ ↦ 1 / t) ([[1, z]]) :=
    continuousOn_const.div continuousOn_id fun t ht ↦
      (lt_of_lt_of_le one_pos (le_of_mem_uIcc hz1 ht)).ne'
  rw [show (fun t ↦ |ρ t| / t) = fun t ↦ |ρ t| * (1 / t) from funext fun t ↦ by ring]
  exact hρ.abs.mul_continuousOn hinvt

private lemma intervalIntegrable_H_sub_const_mul_log (S : SieveDatum) (c : ℝ) {z : ℝ}
    (hz1 : (1 : ℝ) ≤ z) :
    IntervalIntegrable (fun t ↦ S.H t - c * Real.log t) MeasureTheory.volume 1 z :=
  (intervalIntegrable_H S hz1).sub (intervalIntegrable_const_mul_log c hz1)

private lemma mem_range_ceil_filter_iff {z : ℝ} (hz1 : 1 ≤ z) (d : ℕ) :
    d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z) ↔
      d ∈ Finset.Icc 0 ⌊z⌋₊ ∧ d ≠ 0 ∧ (d : ℝ) ≠ z := by
  classical
  rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
  constructor
  · rintro ⟨-, hdpos, hdz⟩
    exact ⟨⟨Nat.zero_le _, Nat.le_floor hdz.le⟩, hdpos.ne', hdz.ne⟩
  · rintro ⟨⟨-, hdN⟩, hd0, hdne⟩
    have hdz : (d : ℝ) < z :=
      lt_of_le_of_ne ((Nat.cast_le.mpr hdN).trans (Nat.floor_le (by linarith))) hdne
    exact ⟨Nat.lt_ceil.mpr hdz, Nat.pos_of_ne_zero hd0, hdz⟩

/-- **Endpoint split at an integral upper limit.**  When `(⌊z⌋₊ : ℝ) = z`, the weighted sum
`∑ k ∈ Finset.Icc 0 ⌊z⌋₊, ψ k * S.h k` equals the sum over `{d | 0 < d ∧ (d : ℝ) < z}` plus the
endpoint contribution `ψ ⌊z⌋₊ * S.h ⌊z⌋₊`. -/
private theorem sum_Icc_floor_mul_h_eq_of_floor_eq (S : SieveDatum) (ψ : ℝ → ℝ) {z : ℝ}
    (hz1 : 1 ≤ z) (hzInt : (⌊z⌋₊ : ℝ) = z) :
    ∑ k ∈ Finset.Icc 0 ⌊z⌋₊, ψ k * S.h k =
      (∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z), S.h d * ψ d) +
        ψ ⌊z⌋₊ * S.h ⌊z⌋₊ := by
  classical
  set N := ⌊z⌋₊ with hN
  have hNpos : 0 < N := by
    have : (0 : ℝ) < (N : ℝ) := by rw [hzInt]; linarith
    exact_mod_cast this
  have hsplit : ∑ k ∈ Finset.Icc 0 N, ψ ↑k * S.h k =
      (∑ d ∈ {d ∈ (Finset.Icc 0 N) | d ≠ 0 ∧ d ≠ N}, ψ ↑d * S.h d) + ψ ↑N * S.h N := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 N) (fun d ↦ d ≠ 0 ∧ d ≠ N)]
    congr 1
    have hcompl : {d ∈ Finset.Icc 0 N | ¬(d ≠ 0 ∧ d ≠ N)} = {0, N} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton,
        not_and, not_not]
      omega
    rw [hcompl, Finset.sum_pair (by omega : (0 : ℕ) ≠ N)]
    simp [S.h_zero]
  rw [hsplit]
  congr 1
  apply Finset.sum_congr _ (fun d _ ↦ mul_comm _ _)
  ext d
  rw [mem_range_ceil_filter_iff hz1 d, Finset.mem_filter, ← hzInt]
  simp

/-- **No endpoint correction at a non-integral upper limit.**  When `(⌊z⌋₊ : ℝ) ≠ z`, the
weighted sum `∑ k ∈ Finset.Icc 0 ⌊z⌋₊, ψ k * S.h k` is exactly the sum over
`{d | 0 < d ∧ (d : ℝ) < z}`. -/
private theorem sum_Icc_floor_mul_h_eq_of_floor_ne (S : SieveDatum) (ψ : ℝ → ℝ) {z : ℝ}
    (hz1 : 1 ≤ z) (hzInt : ¬((⌊z⌋₊ : ℝ) = z)) :
    ∑ k ∈ Finset.Icc 0 ⌊z⌋₊, ψ k * S.h k =
      ∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z), S.h d * ψ d := by
  classical
  have hsplit : ∑ k ∈ Finset.Icc 0 ⌊z⌋₊, ψ ↑k * S.h k =
      ∑ d ∈ {d ∈ (Finset.Icc 0 ⌊z⌋₊) | d ≠ 0}, ψ ↑d * S.h d := by
    rw [← Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 ⌊z⌋₊) (fun d ↦ d ≠ 0)]
    have hcompl : {d ∈ Finset.Icc 0 ⌊z⌋₊ | ¬(d ≠ 0)} = {0} := by
      ext d
      simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton, not_not]
      omega
    rw [hcompl]
    simp [S.h_zero]
  rw [hsplit]
  apply Finset.sum_congr _ (fun d _ ↦ mul_comm _ _)
  ext d
  rw [mem_range_ceil_filter_iff hz1 d, Finset.mem_filter]
  simp [natCast_ne_of_floor_ne hzInt d]

/-- **Abel's partial-summation identity**: `∑_{0 < d < z} h d * G (log d / log z)` equals
`G 1 * H z - ∫ t in 1..z, (deriv G (log t / log z) / (t * log z)) * H t`. -/
theorem abel_identity (S : SieveDatum) (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) (z : ℝ) (hz : 2 ≤ z) :
    (∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
          S.h d * G (Real.log d / Real.log z)) = G 1 * S.H z - ∫ t in (1 : ℝ)..z,
            (deriv G (Real.log t / Real.log z) / (t * Real.log z)) * S.H t := by
  classical
  set L := Real.log z with hLdef
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hLne : L ≠ 0 := hLpos.ne'
  have hderivG : Continuous (deriv G) := hG.continuous_deriv le_rfl
  set φ : ℝ → ℝ := fun t ↦ G (Real.log t / L) with hφ
  set ff' : ℝ → ℝ := fun t ↦ deriv G (Real.log t / L) / (t * L) with hff'
  have hderiv_phi : ∀ t : ℝ, 0 < t → HasDerivAt φ (ff' t) t := by
    intro t ht
    have hlog : HasDerivAt Real.log (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log ht.ne'
    have hGd : HasDerivAt G (deriv G (Real.log t / L)) (Real.log t / L) :=
      (hG.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have heq : deriv G (Real.log t / L) * ((1 / t) / L) = ff' t := by
      simp only [hff']
      rw [div_div, one_div, mul_comm t L]
      field_simp
    exact heq ▸ HasDerivAt.comp t hGd (hlog.div_const L)
  have hf_diff : ∀ t ∈ Set.Icc (1 : ℝ) z, DifferentiableAt ℝ φ t :=
    fun t ht ↦ (hderiv_phi t (by linarith only [ht.1])).differentiableAt
  have hcont_ff' : ContinuousOn ff' (Set.Icc (1 : ℝ) z) := by
    rw [← Set.uIcc_of_le hz1]
    simpa only [hff'] using continuousOn_comp_log_div_mul hderivG hLpos hz1
  have hderiv_eq : Set.EqOn (deriv φ) ff' (Set.Icc (1 : ℝ) z) :=
    fun t ht ↦ (hderiv_phi t (by linarith only [ht.1])).deriv
  have hf_int : MeasureTheory.IntegrableOn (deriv φ) (Set.Icc (1 : ℝ) z) MeasureTheory.volume :=
    (hcont_ff'.integrableOn_compact isCompact_Icc).congr_fun hderiv_eq.symm measurableSet_Icc
  have hAbel := sum_mul_eq_sub_integral_mul₀ (𝕜 := ℝ) S.h S.h_zero z hf_diff hf_int
  have hφz : φ z = G 1 := by
    simp only [hφ, ← hLdef, div_self hLne]
  have hInt : (∫ t in Set.Ioc (1 : ℝ) z, deriv φ t * ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, S.h k) =
        ∫ t in (1 : ℝ)..z, ff' t * S.H t := by
    rw [intervalIntegral.integral_of_le hz1]
    apply MeasureTheory.setIntegral_congr_ae measurableSet_Ioc
    have hae : ∀ᵐ t : ℝ, t ∉ Set.range (fun n : ℕ ↦ (n : ℝ)) := by
      rw [MeasureTheory.ae_iff]
      simp only [not_not]
      exact (Set.countable_range fun n : ℕ ↦ (n : ℝ)).measure_zero MeasureTheory.volume
    filter_upwards [hae] with t htni htmem
    have htpos : 0 < t := by linarith only [htmem.1]
    rw [(hderiv_phi t htpos).deriv,
      (H_ae_summatory S t htpos.le fun n hn ↦ htni ⟨n, hn⟩).symm]
  rw [hφz, hInt] at hAbel
  by_cases hzInt : (⌊z⌋₊ : ℝ) = z
  · set N := ⌊z⌋₊ with hN
    have hIccS : ∑ k ∈ Finset.Icc 0 N, S.h k = S.H z + S.h N := by
      have h := sum_Icc_floor_mul_h_eq_of_floor_eq S (fun _ ↦ (1 : ℝ)) hz1 hzInt
      simp only [one_mul, mul_one] at h
      exact h
    have hIccW : ∑ k ∈ Finset.Icc 0 N, φ ↑k * S.h k =
        (∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
              S.h d * G (Real.log d / L)) + φ ↑N * S.h N :=
      sum_Icc_floor_mul_h_eq_of_floor_eq S φ hz1 hzInt
    have hφN : φ ↑N = G 1 := by rw [hφ]; simp only [hzInt, ← hLdef, div_self hLne]
    rw [hIccW, hIccS, hφN] at hAbel
    rw [← hLdef] at *
    linarith only [hAbel]
  · have htni' : ∀ n : ℕ, (n : ℝ) ≠ z := natCast_ne_of_floor_ne hzInt
    have hHz : S.H z = ∑ k ∈ Finset.Icc 0 ⌊z⌋₊, S.h k :=
      H_ae_summatory S z (by linarith) htni'
    have hIccW : ∑ k ∈ Finset.Icc 0 ⌊z⌋₊, φ ↑k * S.h k =
        ∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
              S.h d * G (Real.log d / L) :=
      sum_Icc_floor_mul_h_eq_of_floor_ne S φ hz1 hzInt
    rw [hIccW, ← hHz] at hAbel
    rw [hAbel]

/-- The Abel integral against the main term `singularSeries S.γ * log t` evaluates to
`singularSeries S.γ * (G 1 * log z - log z * ∫ x in 0..1, G x)`. -/
theorem abel_main_term (S : SieveDatum) (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) (z : ℝ) (hz : 2 ≤ z) :
    (∫ t in (1 : ℝ)..z, (deriv G (Real.log t / Real.log z) / (t * Real.log z)) *
          (PrimeGaps.singularSeries S.γ * Real.log t)) = PrimeGaps.singularSeries S.γ *
          (G 1 * Real.log z - Real.log z * ∫ x in (0 : ℝ)..1, G x) := by
  set L := Real.log z with hLdef
  set singular := PrimeGaps.singularSeries S.γ with hsingulardef
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hLpos : 0 < L := Real.log_pos (by linarith)
  have hLne : L ≠ 0 := hLpos.ne'
  have hderivG : Continuous (deriv G) := hG.continuous_deriv le_rfl
  set f : ℝ → ℝ := fun t ↦ Real.log t / L with hf
  set f' : ℝ → ℝ := fun t ↦ 1 / (t * L) with hf'
  set g : ℝ → ℝ := fun x ↦ deriv G x * x * L * singular with hg
  have hderiv_f : ∀ t ∈ [[(1 : ℝ), z]], HasDerivAt f (f' t) t := by
    intro t ht
    have htpos : (0 : ℝ) < t := by linarith [le_of_mem_uIcc hz1 ht]
    have hlog : HasDerivAt Real.log (1 / t) t := by
      simpa [one_div] using Real.hasDerivAt_log htpos.ne'
    have heq : (1 / t) / L = f' t := by simp only [hf']; rw [div_div]
    exact heq ▸ hlog.div_const L
  have hcont_f' : ContinuousOn f' ([[(1 : ℝ), z]]) := by
    simp only [hf']
    refine continuousOn_const.div (continuous_id'.mul continuous_const).continuousOn fun t ht ↦ ?_
    exact (mul_pos (by linarith [le_of_mem_uIcc hz1 ht]) hLpos).ne'
  have hcont_g : Continuous g := by
    simp only [hg]
    exact ((hderivG.mul continuous_id').mul continuous_const).mul continuous_const
  have hcov := intervalIntegral.integral_comp_mul_deriv hderiv_f hcont_f' hcont_g
  have hf1 : f 1 = 0 := by simp [hf]
  have hfz : f z = 1 := by simp only [hf]; rw [← hLdef, div_self hLne]
  rw [hf1, hfz] at hcov
  have hLHS : (∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * (singular * Real.log t)) =
        ∫ t in (1 : ℝ)..z, (g ∘ f) t * f' t := by
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    have htne : t ≠ 0 := (lt_of_lt_of_le one_pos (le_of_mem_uIcc hz1 ht)).ne'
    simp only [Function.comp_apply, hg, hf, hf']
    field_simp
  rw [hLHS, hcov]
  have hgpull : (∫ x in (0 : ℝ)..1, g x) = (L * singular) * ∫ x in (0 : ℝ)..1, x * deriv G x := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun x _ ↦ by simp only [hg]; ring
  rw [hgpull]
  have hIBP : (∫ x in (0 : ℝ)..1, x * deriv G x) = G 1 - ∫ x in (0 : ℝ)..1, G x := by
    have hu : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt id (1 : ℝ) x := fun x _ ↦ hasDerivAt_id x
    have hv : ∀ x ∈ [[(0 : ℝ), 1]], HasDerivAt G (deriv G x) x :=
      fun x _ ↦ (hG.differentiable (by norm_num)).differentiableAt.hasDerivAt
    have hres := intervalIntegral.integral_mul_deriv_eq_deriv_mul hu hv intervalIntegrable_const
      (hderivG.intervalIntegrable 0 1)
    simp only [id_eq, one_mul, zero_mul, sub_zero] at hres
    exact hres
  rw [hIBP]
  ring

/-- **Abel reduction of the sieve sum.**  Subtracting the main term
`singularSeries S.γ * log z * ∫ x in 0..1, G x` from `∑_{0 < d < z} S.h d * G (log d / log z)`
leaves exactly the Abel transform of the summatory error `t ↦ S.H t - singularSeries S.γ * log t`.
-/
private theorem abel_error_identity (S : SieveDatum) (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G)
    (z : ℝ) (hz : 2 ≤ z) :
    (∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
          S.h d * G (Real.log d / Real.log z)) -
        PrimeGaps.singularSeries S.γ * Real.log z * (∫ x in (0 : ℝ)..1, G x) =
      G 1 * (S.H z - PrimeGaps.singularSeries S.γ * Real.log z) -
        ∫ t in (1 : ℝ)..z, (deriv G (Real.log t / Real.log z) / (t * Real.log z)) *
          (S.H t - PrimeGaps.singularSeries S.γ * Real.log t) := by
  classical
  set singular := PrimeGaps.singularSeries S.γ with hsingular
  set L := Real.log z with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  set ρ : ℝ → ℝ := fun t ↦ S.H t - singular * Real.log t with hρ
  set SigW : ℝ := ∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
          S.h d * G (Real.log d / L) with hSigW
  set M : ℝ := singular * L * (∫ x in (0 : ℝ)..1, G x) with hM
  change SigW - M = G 1 * ρ z - ∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * ρ t
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hAbel := abel_identity S G hG z hz
  have hMain := abel_main_term S G hG z hz
  have hcontfac : ContinuousOn (fun t ↦ deriv G (Real.log t / L) / (t * L)) ([[1, z]]) :=
    continuousOn_comp_log_div_mul (hG.continuous_deriv le_rfl) hLpos hz1
  have hSlogii : IntervalIntegrable
      (fun t ↦ (deriv G (Real.log t / L) / (t * L)) * (singular * Real.log t))
      MeasureTheory.volume 1 z :=
    (intervalIntegrable_const_mul_log singular hz1).continuousOn_mul hcontfac
  have hρintii : IntervalIntegrable (fun t ↦ (deriv G (Real.log t / L) / (t * L)) * ρ t)
      MeasureTheory.volume 1 z :=
    (intervalIntegrable_H_sub_const_mul_log S singular hz1).continuousOn_mul hcontfac
  have hsplit : (∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * S.H t) =
        (∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * (singular * Real.log t)) +
          (∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * ρ t) := by
    rw [← intervalIntegral.integral_add hSlogii hρintii]
    refine intervalIntegral.integral_congr fun t _ ↦ ?_
    simp only [hρ]
    ring
  rw [← hL] at hAbel hMain
  have hAbel' : SigW = G 1 * S.H z -
      ∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * S.H t := by
    rw [hSigW]; exact hAbel
  rw [hM, hAbel', hsplit, hMain]
  simp only [hρ, hL]
  ring

/-- The Abel error form of the sieve sum is at most `Gmax G` times the summatory error
`|S.H z - singularSeries S.γ * log z| + (1 / log z) * ∫ t in 1..z, |S.H t -
singularSeries S.γ * log t| / t`. -/
private theorem abs_abel_error_le (S : SieveDatum) (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G)
    (z : ℝ) (hz : 2 ≤ z) :
    |G 1 * (S.H z - PrimeGaps.singularSeries S.γ * Real.log z) -
        ∫ t in (1 : ℝ)..z, (deriv G (Real.log t / Real.log z) / (t * Real.log z)) *
          (S.H t - PrimeGaps.singularSeries S.γ * Real.log t)| ≤ Gmax G *
          (|S.H z - PrimeGaps.singularSeries S.γ * Real.log z| + (1 / Real.log z) *
                (∫ t in (1 : ℝ)..z,
                  |S.H t - PrimeGaps.singularSeries S.γ * Real.log t| / t)) := by
  classical
  set singular := PrimeGaps.singularSeries S.γ with hsingular
  set L := Real.log z with hL
  have hLpos : 0 < L := Real.log_pos (by linarith)
  set ρ : ℝ → ℝ := fun t ↦ S.H t - singular * Real.log t with hρ
  change |G 1 * ρ z - ∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * ρ t| ≤
      Gmax G * (|ρ z| + (1 / L) * (∫ t in (1 : ℝ)..z, |ρ t| / t))
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hG1 : |G 1| ≤ Gmax G := (Gmax_bounds G hG (by norm_num : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1)).1
  have hderivG : Continuous (deriv G) := hG.continuous_deriv le_rfl
  have hρ_ii : IntervalIntegrable ρ MeasureTheory.volume 1 z :=
    intervalIntegrable_H_sub_const_mul_log S singular hz1
  have habsρt_ii : IntervalIntegrable (fun t ↦ |ρ t| / t)
      MeasureTheory.volume 1 z := intervalIntegrable_abs_div_self hz1 hρ_ii
  have hfull_abs_ii : IntervalIntegrable (fun t ↦ |(deriv G (Real.log t / L) / (t * L)) * ρ t|)
        MeasureTheory.volume 1 z :=
    (hρ_ii.continuousOn_mul (continuousOn_comp_log_div_mul hderivG hLpos hz1)).abs
  have hdom_ii : IntervalIntegrable (fun t ↦ Gmax G * (1 / L) * (|ρ t| / t))
        MeasureTheory.volume 1 z := by
    rw [show (fun t ↦ Gmax G * (1 / L) * (|ρ t| / t)) =
      fun t ↦ (Gmax G * (1 / L)) * (|ρ t| / t) from funext fun t ↦ by ring]
    exact habsρt_ii.const_mul _
  have hpt : ∀ t ∈ Set.Icc (1 : ℝ) z,
      |(deriv G (Real.log t / L) / (t * L)) * ρ t| ≤ Gmax G * (1 / L) * (|ρ t| / t) := by
    intro t ht
    obtain ⟨ht1, htz⟩ := ht
    have htpos : (0 : ℝ) < t := by linarith
    have htL_pos : (0 : ℝ) < t * L := mul_pos htpos hLpos
    have hmem : Real.log t / L ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨div_nonneg (Real.log_nonneg ht1) hLpos.le,
        (div_le_one hLpos).mpr (hL ▸ Real.log_le_log htpos htz)⟩
    have hderiv_bd : |deriv G (Real.log t / L)| ≤ Gmax G := (Gmax_bounds G hG hmem).2
    rw [abs_mul, abs_div, abs_of_pos htL_pos]
    calc |deriv G (Real.log t / L)| / (t * L) * |ρ t| ≤ Gmax G / (t * L) * |ρ t| :=
          mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hderiv_bd htL_pos.le)
            (abs_nonneg _)
      _ = Gmax G * (1 / L) * (|ρ t| / t) := by rw [mul_comm t L]; field_simp
  have hI_abs :
      |∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * ρ t| ≤
        ∫ t in (1 : ℝ)..z, |(deriv G (Real.log t / L) / (t * L)) * ρ t| :=
    intervalIntegral.abs_integral_le_integral_abs hz1
  have hI_mono : (∫ t in (1 : ℝ)..z, |(deriv G (Real.log t / L) / (t * L)) * ρ t|) ≤
        ∫ t in (1 : ℝ)..z, Gmax G * (1 / L) * (|ρ t| / t) :=
    intervalIntegral.integral_mono_on hz1 hfull_abs_ii hdom_ii hpt
  have hI_const : (∫ t in (1 : ℝ)..z, Gmax G * (1 / L) * (|ρ t| / t)) =
        Gmax G * (1 / L) * ∫ t in (1 : ℝ)..z, |ρ t| / t :=
    intervalIntegral.integral_const_mul _ _
  calc |G 1 * ρ z - ∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * ρ t| ≤ |G 1 * ρ z| +
          |∫ t in (1 : ℝ)..z, (deriv G (Real.log t / L) / (t * L)) * ρ t| :=
        abs_sub _ _
    _ ≤ Gmax G * |ρ z| + Gmax G * (1 / L) * ∫ t in (1 : ℝ)..z, |ρ t| / t := by
        have hterm1 : |G 1 * ρ z| ≤ Gmax G * |ρ z| := by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_right hG1 (abs_nonneg _)
        have hterm2 := hI_abs.trans (hI_mono.trans hI_const.le)
        linarith
    _ = Gmax G * (|ρ z| + (1 / L) * (∫ t in (1 : ℝ)..z, |ρ t| / t)) := by ring

/-- Abel's identity turns the deviation of the weighted sum from `singularSeries S.γ * log z *
∫ x in 0..1, G x` into `Gmax G` times the summatory error `|H z - 𝔖 log z| + (1 / log z) *
∫ t in 1..z, |H t - 𝔖 log t| / t`. -/
theorem partial_sum_abel (S : SieveDatum) (G : ℝ → ℝ) (hG : ContDiff ℝ 1 G) (z : ℝ) (hz : 2 ≤ z) :
    |(∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
          S.h d * G (Real.log d / Real.log z)) -
        PrimeGaps.singularSeries S.γ * Real.log z * (∫ x in (0 : ℝ)..1, G x)| ≤ Gmax G *
          (|S.H z - PrimeGaps.singularSeries S.γ * Real.log z| + (1 / Real.log z) *
                (∫ t in (1 : ℝ)..z,
                  |S.H t - PrimeGaps.singularSeries S.γ * Real.log t| / t)) := by
  rw [abel_error_identity S G hG z hz]
  exact abs_abel_error_le S G hG z hz

end PrimeGaps

namespace Real

/-- For `0 < ε` and `0 < t`, `t^(−ε)·log t ≤ ε⁻¹`.  (Via `Real.log_le_rpow_div`:
`log t ≤ t^ε/ε`; multiply by `t^(−ε) > 0`, and `t^(−ε)·t^ε = 1`.) -/
theorem rpow_neg_mul_log_le {ε : ℝ} (hε : 0 < ε) {t : ℝ} (ht : 0 < t) :
    t ^ (-ε) * Real.log t ≤ ε⁻¹ := by
  have hcomb : t ^ (-ε) * t ^ ε = 1 := by rw [← Real.rpow_add ht]; simp
  calc t ^ (-ε) * Real.log t ≤ t ^ (-ε) * (t ^ ε / ε) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div ht.le hε) (Real.rpow_pos_of_pos ht _).le
    _ = ε⁻¹ * (t ^ (-ε) * t ^ ε) := by rw [div_eq_inv_mul]; ring
    _ = ε⁻¹ := by rw [hcomb, mul_one]

end Real

namespace PrimeGaps

/-- On `[1,2]`, `|S.H t| ≤ 1`: the sum defining `S.H t` has at most the single
term `d = 1` (`0 < d ∧ (d:ℝ) < t ≤ 2` forces `d = 1`), and `S.h 1 = 1`. -/
theorem H_abs_le_one_on_Icc12 (S : SieveDatum) (t : ℝ) (ht2 : t ≤ 2) : |S.H t| ≤ 1 := by
  unfold SieveDatum.H
  have hh1 : S.h 1 = 1 := by rw [S.h_squarefree_eq_prod 1 (by simp)]; simp
  have hsub : ((Finset.range ⌈t⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < t)) ⊆ {1} := by
    intro d hd
    rw [Finset.mem_filter] at hd
    obtain ⟨-, hdpos, hdt⟩ := hd
    simp only [Finset.mem_singleton]
    by_contra hne
    have : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast (by omega : 2 ≤ d)
    linarith
  rcases Finset.subset_singleton_iff.mp hsub with hempty | hsingle
  · rw [hempty]; simp
  · rw [hsingle]; simp [hh1]

/-- **Power-integral estimate.** For `z ≥ 2`, `∫₂ᶻ t^(−9/8) dt ≤ 8`.
Mathlib's `integral_rpow` evaluates the integral as `8·(2^(−1/8) − z^(−1/8))`, and
`2^(−1/8) ≤ 1 < 1 + z^(−1/8)`. -/
theorem integral_rpow_neg_nine_eighths_le (z : ℝ) (hz : 2 ≤ z) :
    (∫ t in (2 : ℝ)..z, t ^ (-9 / 8 : ℝ)) ≤ 8 := by
  have h0 : (0 : ℝ) ∉ [[(2 : ℝ), z]] := by
    rw [Set.uIcc_of_le (by linarith : (2 : ℝ) ≤ z)]
    simp only [Set.mem_Icc, not_and, not_le]
    intro h; linarith
  rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩),
    show (-9 / 8 + 1 : ℝ) = -(1 / 8) by norm_num,
    div_le_iff_of_neg (by norm_num : (-(1 / 8) : ℝ) < 0)]
  have hz18 : (0 : ℝ) < z ^ (-(1 / 8) : ℝ) := Real.rpow_pos_of_pos (by linarith) _
  have h218 : (2 : ℝ) ^ (-(1 / 8) : ℝ) ≤ 1 := by
    rw [Real.rpow_neg (by norm_num), inv_le_one_iff₀]
    right
    exact Real.one_le_rpow (by norm_num) (by norm_num)
  linarith only [hz18, h218]

/-- **Power-weighted tail estimate.**  If `|ρ t| ≤ a + b * t ^ (-1/8)` on `[2, z]` with
`a, b ≥ 0`, then `∫ t in 2..z, |ρ t| / t ≤ a * log z + 8 * b`; the second term uses
`∫ t in 2..z, t ^ (-9/8) ≤ 8`. -/
private theorem integral_abs_div_le_of_rpow_bound (ρ : ℝ → ℝ) (a b z : ℝ) (ha : 0 ≤ a)
    (hb : 0 ≤ b) (hz : 2 ≤ z)
    (hii : IntervalIntegrable (fun t ↦ |ρ t| / t) MeasureTheory.volume 2 z)
    (hpt : ∀ t ∈ Set.Icc (2 : ℝ) z, |ρ t| ≤ a + b * t ^ (-1 / 8 : ℝ)) :
    (∫ t in (2 : ℝ)..z, |ρ t| / t) ≤ a * Real.log z + 8 * b := by
  have hzpos : (0 : ℝ) < z := by linarith
  set g : ℝ → ℝ := fun t ↦ a * (1 / t) + b * t ^ (-9 / 8 : ℝ) with hg
  have htne : ∀ t ∈ Set.uIcc (2 : ℝ) z, t ≠ 0 := fun t ht ↦
    (lt_of_lt_of_le (by norm_num) (le_of_mem_uIcc hz ht)).ne'
  have hii_inv : IntervalIntegrable (fun t : ℝ ↦ 1 / t) MeasureTheory.volume 2 z :=
    (continuousOn_const.div continuousOn_id htne).intervalIntegrable
  have hii_pow : IntervalIntegrable (fun t : ℝ ↦ t ^ (-9 / 8 : ℝ)) MeasureTheory.volume 2 z :=
    (continuousOn_id.rpow_const fun t ht ↦ Or.inl (htne t ht)).intervalIntegrable
  have hg_ii : IntervalIntegrable g MeasureTheory.volume 2 z := by
    rw [hg]; exact (hii_inv.const_mul _).add (hii_pow.const_mul _)
  have hptg : ∀ t ∈ Set.Icc (2 : ℝ) z, |ρ t| / t ≤ g t := by
    intro t ht
    have htpos : (0 : ℝ) < t := by linarith only [ht.1]
    have hrpow_eq : (t ^ (-1 / 8 : ℝ)) / t = t ^ (-9 / 8 : ℝ) := by
      rw [div_eq_mul_inv, ← Real.rpow_neg_one t, ← Real.rpow_add htpos]
      norm_num
    calc |ρ t| / t ≤ (a + b * t ^ (-1 / 8 : ℝ)) / t := by gcongr; exact hpt t ht
      _ = g t := by
          rw [hg, add_div, show b * t ^ (-1 / 8 : ℝ) / t = b * (t ^ (-1 / 8 : ℝ) / t) by ring,
            hrpow_eq]
          simp only [mul_one_div]
  have hg_split : (∫ t in (2 : ℝ)..z, g t) = a * (∫ t in (2 : ℝ)..z, 1 / t) +
        b * (∫ t in (2 : ℝ)..z, t ^ (-9 / 8 : ℝ)) := by
    rw [hg, intervalIntegral.integral_add (hii_inv.const_mul _) (hii_pow.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hint_inv : (∫ t in (2 : ℝ)..z, 1 / t) = Real.log (z / 2) := by
    rw [integral_one_div_of_pos (by norm_num) (by linarith)]
  have hint_inv_le : (∫ t in (2 : ℝ)..z, 1 / t) ≤ Real.log z := by
    rw [hint_inv]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by norm_num)]; linarith only [hzpos]
  have hint_inv_nn : (0 : ℝ) ≤ (∫ t in (2 : ℝ)..z, 1 / t) := by
    rw [hint_inv]; apply Real.log_nonneg
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hint_pow_le : (∫ t in (2 : ℝ)..z, t ^ (-9 / 8 : ℝ)) ≤ 8 :=
    integral_rpow_neg_nine_eighths_le z hz
  calc (∫ t in (2 : ℝ)..z, |ρ t| / t) ≤ ∫ t in (2 : ℝ)..z, g t :=
        intervalIntegral.integral_mono_on hz hii hg_ii hptg
    _ = a * (∫ t in (2 : ℝ)..z, 1 / t) + b * (∫ t in (2 : ℝ)..z, t ^ (-9 / 8 : ℝ)) := hg_split
    _ ≤ a * Real.log z + b * 8 := by gcongr
    _ = a * Real.log z + 8 * b := by ring

/-- The summatory error `|H z - 𝔖 log z| + (1 / log z) * ∫ t in 1..z, |H t - 𝔖 log t| / t` is at
most `E₁ * 𝔖 * (1 + ellV V) + E₂ * τ V * log (2 * V * z) / log z`, with `E₁`, `E₂` depending only
on `S.A₁` and `S.A₃`. -/
theorem H_error_bound : ∃ E₁ E₂ : ℝ → ℝ → ℝ,
      (∀ A₁ A₃ : ℝ, 0 < E₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < E₂ A₁ A₃) ∧
      ∀ (S : SieveDatum) (z : ℝ), 2 ≤ z →
        |S.H z - PrimeGaps.singularSeries S.γ * Real.log z| + (1 / Real.log z) * (∫ t in (1 : ℝ)..z,
                |S.H t - PrimeGaps.singularSeries S.γ * Real.log t| / t) ≤
        E₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
          E₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * Real.log (2 * S.V * z) / Real.log z := by
  obtain ⟨C₁, C₂, hC₁, hC₂, hH⟩ := PrimeGaps.slem_H_error_assembly
  refine ⟨fun A₁ A₃ ↦ 2 * C₁ A₁ A₃ + 1, fun A₁ A₃ ↦ 16 * C₂ A₁ A₃ + 1 / Real.log 2, ?_, ?_, ?_⟩
  · intro A₁ A₃; have := hC₁ A₁ A₃; positivity
  · intro A₁ A₃
    have := hC₂ A₁ A₃
    have hl2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  intro S z hz
  set singular := PrimeGaps.singularSeries S.γ with hsingular
  set D₁ := C₁ S.A₁ S.A₃ with hD₁
  set D₂ := C₂ S.A₁ S.A₃ with hD₂
  set τ : ℝ := (#S.V.divisors : ℝ) with hτ
  set ℓ : ℝ := ellV S.V with hℓ
  set Lz : ℝ := Real.log z with hLz
  set Λz : ℝ := Real.log (2 * S.V * z) with hΛz
  set ρ : ℝ → ℝ := fun t ↦ S.H t - singular * Real.log t with hρ
  have hz1 : (1 : ℝ) ≤ z := by linarith
  have hzpos : (0 : ℝ) < z := by linarith
  have hsingularpos : 0 < singular := PrimeGaps.singularSeries_pos S
  have hD₁pos : 0 < D₁ := hC₁ S.A₁ S.A₃
  have hD₂pos : 0 < D₂ := hC₂ S.A₁ S.A₃
  have hℓnn : 0 ≤ ℓ := by rw [hℓ]; exact PrimeGaps.ellV_nonneg _
  have hτ1 : (1 : ℝ) ≤ τ := by
    rw [hτ]
    have : 1 ≤ #S.V.divisors :=
      Nat.one_le_iff_ne_zero.mpr (by simp [Nat.divisors_eq_empty, S.V_pos.ne'])
    exact_mod_cast this
  have hLzpos : 0 < Lz := by rw [hLz]; exact Real.log_pos (by linarith)
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLz_ge : Real.log 2 ≤ Lz := by rw [hLz]; exact Real.log_le_log (by norm_num) hz
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast S.V_pos
  have hΛz_ge : Lz ≤ Λz := by
    rw [hLz, hΛz]
    exact Real.log_le_log hzpos (le_mul_of_one_le_left hzpos.le (by linarith only [hV1]))
  have hΛzpos : 0 < Λz := lt_of_lt_of_le hLzpos hΛz_ge
  clear_value singular D₁ D₂ τ ℓ Lz Λz
  have habsρt_ii1 : IntervalIntegrable (fun t ↦ |ρ t| / t) MeasureTheory.volume 1 z :=
    intervalIntegrable_abs_div_self hz1 (intervalIntegrable_H_sub_const_mul_log S singular hz1)
  have habsρt_ii12 : IntervalIntegrable (fun t ↦ |ρ t| / t) MeasureTheory.volume 1 2 := by
    apply habsρt_ii1.mono_set
    rw [Set.uIcc_of_le hz1, Set.uIcc_of_le (by norm_num : (1 : ℝ) ≤ 2)]
    exact Set.Icc_subset_Icc le_rfl hz
  have habsρt_ii2z : IntervalIntegrable (fun t ↦ |ρ t| / t) MeasureTheory.volume 2 z := by
    apply habsρt_ii1.mono_set
    rw [Set.uIcc_of_le hz1, Set.uIcc_of_le hz]
    exact Set.Icc_subset_Icc (by norm_num) le_rfl
  have hsplit : (∫ t in (1 : ℝ)..z, |ρ t| / t) =
      (∫ t in (1 : ℝ)..2, |ρ t| / t) + ∫ t in (2 : ℝ)..z, |ρ t| / t :=
    (intervalIntegral.integral_add_adjacent_intervals habsρt_ii12 habsρt_ii2z).symm
  have hgoal_eq : (∫ t in (1 : ℝ)..z, |S.H t - singular * Real.log t| / t) =
      ∫ t in (1 : ℝ)..z, |ρ t| / t :=
    intervalIntegral.integral_congr fun t _ ↦ by simp only [hρ]
  have bound_1z2 : (∫ t in (1 : ℝ)..2, |ρ t| / t) ≤ 1 + singular * Real.log 2 := by
    have hpt : ∀ t ∈ Set.Icc (1 : ℝ) 2, |ρ t| / t ≤ 1 + singular * Real.log 2 := by
      intro t ht
      obtain ⟨ht1, ht2⟩ := ht
      have htpos : (0 : ℝ) < t := by linarith
      have hlogt_nn : (0 : ℝ) ≤ Real.log t := Real.log_nonneg ht1
      have hlogt_le : Real.log t ≤ Real.log 2 := Real.log_le_log htpos ht2
      have habsρ : |ρ t| ≤ 1 + singular * Real.log 2 := by
        have h1 : |ρ t| ≤ |S.H t| + |singular * Real.log t| := by
          rw [hρ]; exact abs_sub _ _
        rw [abs_of_nonneg (by positivity : (0 : ℝ) ≤ singular * Real.log t)] at h1
        linarith [H_abs_le_one_on_Icc12 S t ht2,
          mul_le_mul_of_nonneg_left hlogt_le hsingularpos.le]
      have hinvt : |ρ t| / t ≤ |ρ t| := by
        rw [div_le_iff₀ htpos]
        exact le_mul_of_one_le_right (abs_nonneg (ρ t)) ht1
      linarith
    calc (∫ t in (1 : ℝ)..2, |ρ t| / t) ≤ ∫ _ in (1 : ℝ)..2, (1 + singular * Real.log 2) :=
          intervalIntegral.integral_mono_on (by norm_num) habsρt_ii12
            intervalIntegrable_const hpt
      _ = 1 + singular * Real.log 2 := by
          rw [intervalIntegral.integral_const]; norm_num
  have bound_2z : (∫ t in (2 : ℝ)..z, |ρ t| / t) ≤
      D₁ * singular * (1 + ℓ) * Lz + 8 * (D₂ * τ * Λz) := by
    rw [hLz]
    refine integral_abs_div_le_of_rpow_bound ρ _ _ z (by positivity) (by positivity) hz
      habsρt_ii2z ?_
    intro t ht
    obtain ⟨ht2, htz⟩ := ht
    have htpos : (0 : ℝ) < t := by linarith
    have hHt : |S.H t - singular * Real.log t| ≤
        D₁ * singular * (1 + ℓ) + D₂ * τ * t ^ (-1 / 8 : ℝ) * Real.log (2 * S.V * t) := by
      rw [hsingular, hD₁, hℓ, hD₂, hτ]; exact hH S t ht2
    have hlogle : Real.log (2 * S.V * t) ≤ Λz := by
      rw [hΛz]
      exact Real.log_le_log (mul_pos (by linarith only [hV1]) htpos)
        (mul_le_mul_of_nonneg_left htz (by positivity))
    have hρt : |ρ t| = |S.H t - singular * Real.log t| := by rw [hρ]
    rw [hρt]
    calc |S.H t - singular * Real.log t|
        ≤ D₁ * singular * (1 + ℓ) + D₂ * τ * t ^ (-1 / 8 : ℝ) * Real.log (2 * S.V * t) := hHt
      _ ≤ D₁ * singular * (1 + ℓ) + D₂ * τ * Λz * t ^ (-1 / 8 : ℝ) := by
          have hcoef : (0 : ℝ) ≤ D₂ * τ * (t ^ (-1 / 8 : ℝ)) := by positivity
          nlinarith only [mul_le_mul_of_nonneg_left hlogle hcoef]
  have bound_z : |ρ z| ≤ D₁ * singular * (1 + ℓ) + 8 * (D₂ * τ * Λz) / Lz := by
    have hHz : |S.H z - singular * Lz| ≤
        D₁ * singular * (1 + ℓ) + D₂ * τ * z ^ (-1 / 8 : ℝ) * Λz := by
      rw [hsingular, hLz, hD₁, hℓ, hD₂, hτ, hΛz]; exact hH S z hz
    have hrp : z ^ (-1 / 8 : ℝ) ≤ 8 / Lz := by
      rw [le_div_iff₀ hLzpos]
      have h8 : z ^ (-1 / 8 : ℝ) * Real.log z ≤ 8 := by
        rw [show (-1 / 8 : ℝ) = -(1 / 8) by norm_num]
        exact (Real.rpow_neg_mul_log_le (ε := 1 / 8) (by norm_num) hzpos).trans (by norm_num)
      rw [hLz]; linarith
    have hρz : |ρ z| = |S.H z - singular * Lz| := by rw [hρ, hLz]
    rw [hρz]
    have hkey : D₂ * τ * z ^ (-1 / 8 : ℝ) * Λz ≤ 8 * (D₂ * τ * Λz) / Lz := by
      rw [show D₂ * τ * z ^ (-1 / 8 : ℝ) * Λz = (D₂ * τ * Λz) * z ^ (-1 / 8 : ℝ) by ring,
        show 8 * (D₂ * τ * Λz) / Lz = (D₂ * τ * Λz) * (8 / Lz) by ring]
      exact mul_le_mul_of_nonneg_left hrp (by positivity)
    linarith only [hHz, hkey]
  beta_reduce
  rw [← hD₁, ← hD₂]
  change |S.H z - singular * Lz| + 1 / Lz * (∫ t in (1 : ℝ)..z, |S.H t - singular * Real.log t| /
    t) ≤ (2 * D₁ + 1) * singular * (1 + ℓ) + (16 * D₂ + 1 / Real.log 2) * τ * Λz / Lz
  have hρz' : |S.H z - singular * Lz| = |ρ z| := by rw [hρ, hLz]
  rw [hgoal_eq, hsplit, hρz']
  have hinvLz_pos : (0 : ℝ) < 1 / Lz := by positivity
  have hmul : 1 / Lz * ((∫ t in (1 : ℝ)..2, |ρ t| / t) + (∫ t in (2 : ℝ)..z, |ρ t| / t)) ≤
      1 / Lz * ((1 + singular * Real.log 2) + (D₁ * singular * (1 + ℓ) * Lz + 8 * (D₂ * τ * Λz))) :=
    mul_le_mul_of_nonneg_left (by linarith only [bound_1z2, bound_2z]) hinvLz_pos.le
  have hinv_le : 1 / Lz ≤ 1 / Real.log 2 := one_div_le_one_div_of_le hlog2pos hLz_ge
  have htΛLz_ge1 : (1 : ℝ) ≤ τ * Λz / Lz := by
    rw [le_div_iff₀ hLzpos, one_mul]
    exact hΛz_ge.trans (le_mul_of_one_le_left hΛzpos.le hτ1)
  have e8' : 8 * (D₂ * τ * Λz) / Lz = 8 * (D₂ * (τ * Λz / Lz)) := by field_simp
  have rhs_eq : (2 * D₁ + 1) * singular * (1 + ℓ) + (16 * D₂ + 1 / Real.log 2) * τ * Λz / Lz =
      (2 * (D₁ * singular * (1 + ℓ)) + singular * (1 + ℓ)) +
        (16 * (D₂ * (τ * Λz / Lz)) + (1 / Real.log 2) * (τ * Λz / Lz)) := by
    field_simp
  rw [rhs_eq]
  have hmid : 1 / Lz * (1 + singular * Real.log 2) ≤
      singular * (1 + ℓ) + (1 / Real.log 2) * (τ * Λz / Lz) := by
    have hA : singular * (Real.log 2 / Lz) ≤ singular * (1 + ℓ) := by
      refine mul_le_mul_of_nonneg_left ?_ hsingularpos.le
      have hlog2Lz : Real.log 2 / Lz ≤ 1 := (div_le_one hLzpos).mpr hLz_ge
      linarith only [hlog2Lz, hℓnn]
    have hB : 1 / Lz ≤ (1 / Real.log 2) * (τ * Λz / Lz) :=
      calc 1 / Lz ≤ 1 / Real.log 2 := hinv_le
        _ = (1 / Real.log 2) * 1 := by ring
        _ ≤ (1 / Real.log 2) * (τ * Λz / Lz) :=
            mul_le_mul_of_nonneg_left htΛLz_ge1 (by positivity)
    rw [show 1 / Lz * (1 + singular * Real.log 2) = 1 / Lz + singular * (Real.log 2 / Lz) from by
      field_simp]
    linarith
  have hmul2 : 1 / Lz * ((∫ t in (1 : ℝ)..2, |ρ t| / t) + (∫ t in (2 : ℝ)..z, |ρ t| / t)) ≤
      1 / Lz * (1 + singular * Real.log 2) + (D₁ * singular * (1 + ℓ) + 8 * (D₂ * (τ * Λz / Lz))) :=
    hmul.trans_eq (by field_simp)
  rw [e8'] at bound_z
  linarith only [bound_z, hmul2, hmid]

private lemma one_le_one_add_log_natCast (e : ℕ) : (1 : ℝ) ≤ 1 + Real.log e := by
  linarith [Real.log_natCast_nonneg e]

/-- The logarithmically weighted `bTilde` series is summable:
`Summable (fun e ↦ |S.bTilde e| * (1 + log e))`, majorised by
`3 * |S.bDefect e| * (e.divisors.card) * √e`. -/
private theorem summable_abs_bTilde_mul_log (S : SieveDatum) :
    Summable (fun e : ℕ ↦ |S.bTilde e| * (1 + Real.log e)) := by
  have hmaj3 : Summable (fun e ↦ 3 * (|S.bDefect e| * (#e.divisors : ℝ) * √e)) :=
    (PrimeGaps.bDefect_tau_sqrt_summable S).mul_left 3
  refine hmaj3.of_nonneg_of_le (fun e ↦ ?_) (fun e ↦ PrimeGaps.abs_bTilde_mul_log_le S e)
  exact mul_nonneg (abs_nonneg (S.bTilde e)) (by linarith only [one_le_one_add_log_natCast e])

/-- The singular series is dominated by the logarithmically weighted `bTilde` sum:
`singularSeries S.γ ≤ ∑' e, |S.bTilde e| * (1 + log e)`. -/
private theorem singularSeries_le_tsum_abs_bTilde_mul_log (S : SieveDatum) :
    PrimeGaps.singularSeries S.γ ≤ ∑' e : ℕ, |S.bTilde e| * (1 + Real.log e) := by
  rw [PrimeGaps.slem_singularSeries_bTilde_bridge S]
  have hsummand : ∀ e : ℕ, |S.bTilde e| ≤ |S.bTilde e| * (1 + Real.log e) := fun e ↦
    le_mul_of_one_le_right (abs_nonneg (S.bTilde e)) (one_le_one_add_log_natCast e)
  have hsummable : Summable (fun e ↦ |S.bTilde e| * (1 + Real.log e)) :=
    summable_abs_bTilde_mul_log S
  have hsummable2 : Summable (fun e ↦ |S.bTilde e|) :=
    hsummable.of_nonneg_of_le (fun e ↦ abs_nonneg _) hsummand
  have hbt_summable : Summable (fun e ↦ S.bTilde e) := hsummable2.of_abs
  have h1 : ∑' e, S.bTilde e ≤ ∑' e, |S.bTilde e| :=
    Summable.tsum_mono hbt_summable hsummable2 (fun e ↦ le_abs_self _)
  have h2 : ∑' e, |S.bTilde e| ≤ ∑' e, |S.bTilde e| * (1 + Real.log e) :=
    Summable.tsum_mono hsummable2 hsummable hsummand
  have hVtot : (S.V.totient : ℝ) / S.V ≤ 1 := by
    rw [div_le_one (by exact_mod_cast S.V_pos)]
    exact_mod_cast Nat.totient_le S.V
  have htsum_nn : (0 : ℝ) ≤ ∑' e, S.bTilde e := by
    have hpos := PrimeGaps.singularSeries_pos S
    rw [PrimeGaps.slem_singularSeries_bTilde_bridge S] at hpos
    by_contra hneg
    push Not at hneg
    have hVtot_nn : (0 : ℝ) ≤ (S.V.totient : ℝ) / S.V := by positivity
    linarith only [hpos, mul_nonneg hVtot_nn (neg_nonneg.mpr hneg.le)]
  calc (S.V.totient : ℝ) / S.V * ∑' e, S.bTilde e
      ≤ 1 * ∑' e, S.bTilde e := mul_le_mul_of_nonneg_right hVtot htsum_nn
    _ = ∑' e, S.bTilde e := by ring
    _ ≤ ∑' e : ℕ, |S.bTilde e| * (1 + Real.log e) := le_trans h1 h2

/-- The Mertens-type sum `ellV V = ∑_{p ∣ V} log p / (p - 1)` is at most the number of
divisors of `V`. -/
private theorem ellV_le_card_divisors (S : SieveDatum) : ellV S.V ≤ (#S.V.divisors : ℝ) := by
  have step1 : ellV S.V ≤ (#S.V.primeFactors : ℝ) := by
    unfold ellV
    calc ∑ p ∈ S.V.primeFactors, Real.log p / ((p : ℝ) - 1) ≤ ∑ p ∈ S.V.primeFactors, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro p hp
          have hpr : (1 : ℝ) < (p : ℝ) := by
            have : (2 : ℝ) ≤ (p : ℝ) := by
              exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
            linarith
          rw [div_le_one (by linarith)]
          linarith [Real.log_le_sub_one_of_pos (x := (p : ℝ)) (by linarith)]
      _ = (#S.V.primeFactors : ℝ) := by simp
  have step2 : (#S.V.primeFactors : ℝ) ≤ (#S.V.divisors : ℝ) := by
    have hsub : S.V.primeFactors ⊆ S.V.divisors := fun p hp ↦
      Nat.mem_divisors.mpr ⟨Nat.dvd_of_mem_primeFactors hp, S.V_pos.ne'⟩
    exact_mod_cast Finset.card_le_card hsub
  exact step1.trans step2

/-- `𝔖 * (1 + ellV V) ≤ K * 𝔖 * S.L + K * τ V * log (2 * V * z) / log z`, with `K` depending only
on `S.A₁` and `S.A₃`. -/
theorem singularSeries_logV_bridge : ∃ K : ℝ → ℝ → ℝ, (∀ A₁ A₃ : ℝ, 0 < K A₁ A₃) ∧
      ∀ (S : SieveDatum) (z : ℝ), 2 ≤ z → PrimeGaps.singularSeries S.γ * (1 + ellV S.V) ≤
          K S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * S.L + K S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                Real.log (2 * S.V * z) / Real.log z := by
  obtain ⟨Kb, hKb, hKble⟩ := PrimeGaps.bTilde_log_tsum_uniform
  have hS_le : ∀ S : SieveDatum, PrimeGaps.singularSeries S.γ ≤ Kb S.A₁ S.A₃ := fun S ↦
    (singularSeries_le_tsum_abs_bTilde_mul_log S).trans (hKble S)
  have hlV_le : ∀ S : SieveDatum, ellV S.V ≤ (#S.V.divisors : ℝ) := ellV_le_card_divisors
  refine ⟨fun A₁ A₃ ↦ 2 * (Kb A₁ A₃ + 1), fun A₁ A₃ ↦ by have := hKb A₁ A₃; linarith, ?_⟩
  intro S z hz
  set K := 2 * (Kb S.A₁ S.A₃ + 1) with hKdef
  have hKpos : 0 < K := by rw [hKdef]; have := hKb S.A₁ S.A₃; linarith
  have hsingular := hS_le S
  have hsingularpos := PrimeGaps.singularSeries_pos S
  have hlV := hlV_le S
  have hτ1 : (1 : ℝ) ≤ (#S.V.divisors : ℝ) := by
    have : 1 ≤ #S.V.divisors := Nat.one_le_iff_ne_zero.mpr (by
      simp [Nat.divisors_eq_empty, S.V_pos.ne'])
    exact_mod_cast this
  have hlogz_pos : 0 < Real.log z := Real.log_pos (by linarith)
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast S.V_pos
  have hratio : (1 : ℝ) ≤ Real.log (2 * S.V * z) / Real.log z := by
    rw [le_div_iff₀ hlogz_pos, one_mul]
    exact Real.log_le_log (by linarith) (le_mul_of_one_le_left (by linarith) (by linarith))
  have hL : 0 ≤ S.L := S.L_nonneg
  have hstep1 : PrimeGaps.singularSeries S.γ * (1 + ellV S.V) ≤
      PrimeGaps.singularSeries S.γ * (1 + (#S.V.divisors : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hsingularpos.le
  have hstep2 : PrimeGaps.singularSeries S.γ * (1 + (#S.V.divisors : ℝ)) ≤
      Kb S.A₁ S.A₃ * (1 + (#S.V.divisors : ℝ)) :=
    mul_le_mul_of_nonneg_right hsingular (by linarith)
  have hstep3 : Kb S.A₁ S.A₃ * (1 + (#S.V.divisors : ℝ)) ≤ K * (#S.V.divisors : ℝ) := by
    rw [hKdef]
    linarith only [mul_nonneg (hKb S.A₁ S.A₃).le
      (by linarith only [hτ1] : (0 : ℝ) ≤ (S.V.divisors.card : ℝ) - 1), hτ1]
  have hstep4 : K * (#S.V.divisors : ℝ) ≤
      K * (#S.V.divisors : ℝ) * Real.log (2 * S.V * z) / Real.log z := by
    rw [mul_div_assoc]
    exact le_mul_of_one_le_right (mul_nonneg hKpos.le (by linarith only [hτ1])) hratio
  have hfirst : 0 ≤ K * PrimeGaps.singularSeries S.γ * S.L := by positivity
  calc PrimeGaps.singularSeries S.γ * (1 + ellV S.V)
      ≤ K * (#S.V.divisors : ℝ) * Real.log (2 * S.V * z) / Real.log z := by
        linarith only [hstep1, hstep2, hstep3, hstep4]
    _ ≤ K * PrimeGaps.singularSeries S.γ * S.L +
          K * (#S.V.divisors : ℝ) * Real.log (2 * S.V * z) / Real.log z := by
        linarith only [hfirst]

/-- The weighted sieve sum `∑_{0 < d < z} h d * G (log d / log z)` differs from
`singularSeries S.γ * log z * ∫ x in 0..1, G x` by at most
`(C₁ * 𝔖 * S.L + C₂ * τ V * log (2 * V * z) / log z) * Gmax G`. -/
@[pg_tag "bg246" "lem_partial_sum"]
theorem lem_partial_sum : ∃ (C₁ : ℝ → ℝ → ℝ → ℝ) (C₂ : ℝ → ℝ → ℝ),
      (∀ A₁ A₂ A₃ : ℝ, 0 < C₁ A₁ A₂ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < C₂ A₁ A₃) ∧
      ∀ (S : SieveDatum) (G : ℝ → ℝ), ContDiff ℝ 1 G →
      ∀ z : ℝ, 2 ≤ z →
        |(∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
              S.h d * G (Real.log d / Real.log z)) -
            PrimeGaps.singularSeries S.γ * Real.log z * (∫ x in (0 : ℝ)..1, G x)| ≤
          C₁ S.A₁ S.A₂ S.A₃ * PrimeGaps.singularSeries S.γ * S.L * Gmax G +
            C₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                Real.log (2 * S.V * z) / Real.log z * Gmax G := by
  obtain ⟨E₁, E₂, hE₁, hE₂, hHerr⟩ := H_error_bound
  obtain ⟨K, hK, hbridge⟩ := singularSeries_logV_bridge
  refine ⟨fun A₁ _ A₃ ↦ E₁ A₁ A₃ * K A₁ A₃, fun A₁ A₃ ↦ E₁ A₁ A₃ * K A₁ A₃ + E₂ A₁ A₃, ?_, ?_, ?_⟩
  · intro A₁ _ A₃; exact mul_pos (hE₁ A₁ A₃) (hK A₁ A₃)
  · intro A₁ A₃; exact add_pos (mul_pos (hE₁ A₁ A₃) (hK A₁ A₃)) (hE₂ A₁ A₃)
  · intro S G hG z hz
    have habel := partial_sum_abel S G hG z hz
    have hHb := hHerr S z hz
    have hbr := hbridge S z hz
    have hGmax : (0 : ℝ) ≤ Gmax G := Gmax_nonneg G hG
    have hHb' := mul_le_mul_of_nonneg_left hHb hGmax
    have hbr' := mul_le_mul_of_nonneg_left hbr (hE₁ S.A₁ S.A₃).le
    have hbr'' := mul_le_mul_of_nonneg_right hbr' hGmax
    change _ ≤ (E₁ S.A₁ S.A₃ * K S.A₁ S.A₃) * PrimeGaps.singularSeries S.γ * S.L * Gmax G +
        (E₁ S.A₁ S.A₃ * K S.A₁ S.A₃ + E₂ S.A₁ S.A₃) * (#S.V.divisors : ℝ) *
            Real.log (2 * S.V * z) / Real.log z * Gmax G
    calc _
        ≤ Gmax G * (|S.H z - PrimeGaps.singularSeries S.γ * Real.log z| + (1 / Real.log z) *
                    (∫ t in (1 : ℝ)..z,
                      |S.H t - PrimeGaps.singularSeries S.γ * Real.log t| / t)) := habel
      _ ≤ Gmax G * (E₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
              E₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * Real.log (2 * S.V * z) / Real.log z) := hHb'
      _ ≤ _ := by
            have hexp : Gmax G * (E₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
                      E₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * Real.log (2 * S.V * z) /
                        Real.log z) =
                  E₁ S.A₁ S.A₃ * (PrimeGaps.singularSeries S.γ * (1 + ellV S.V)) * Gmax G +
                    E₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                          Real.log (2 * S.V * z) / Real.log z * Gmax G := by
              ring
            have hrhs : E₁ S.A₁ S.A₃ * K S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * S.L * Gmax G +
                    (E₁ S.A₁ S.A₃ * K S.A₁ S.A₃ + E₂ S.A₁ S.A₃) * (#S.V.divisors : ℝ) *
                        Real.log (2 * S.V * z) / Real.log z * Gmax G = E₁ S.A₁ S.A₃ *
                      (K S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * S.L +
                        K S.A₁ S.A₃ * (#S.V.divisors : ℝ) * Real.log (2 * S.V * z) /
                          Real.log z) *
                      Gmax G + E₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                          Real.log (2 * S.V * z) / Real.log z * Gmax G := by
              ring
            rw [hexp, hrhs]
            linarith only [hbr'']

end PrimeGaps
