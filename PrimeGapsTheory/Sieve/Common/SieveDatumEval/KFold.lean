/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Sieve.Common.SieveDatumEval.LayerG

/-!
# The k-fold partial sum

Assembles the layer estimates into the k-fold partial-summation bound.

## Main results

* `sieveDatum_kfold_partial_sum`
-/

@[expose] public section

open scoped Finset

open MeasureTheory

namespace PrimeGaps


/-- **Truncated sieve sum bound.**  Evaluating the `H`-asymptotic at `t = ⌈z⌉₊ + 1 ≤ z ^ 2`,
`∑_{d ≤ ⌈z⌉₊} S.h d ≤ 2 𝔖 log z + ch₁ 𝔖 (1 + ellV V) +
ch₂ τ V (z ^ (-1/8) * (log (2 V z) + log z))`. -/
private theorem sum_h_range_ceil_succ_le (S : SieveDatum) (z : ℝ) (hz : 2 ≤ z)
    (ch₁ ch₂ : ℝ) (hch₂ : 0 ≤ ch₂)
    (hHasymp : ∀ t : ℝ, 2 ≤ t →
      |S.H t - PrimeGaps.singularSeries S.γ * Real.log t| ≤
        ch₁ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
          ch₂ * (#S.V.divisors : ℝ) * t ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * t)) :
    ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d ≤ 2 * PrimeGaps.singularSeries S.γ * Real.log z +
        ch₁ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
        ch₂ * (#S.V.divisors : ℝ) *
          (z ^ (-(1 : ℝ) / 8) * (Real.log (2 * ↑S.V * z) + Real.log z)) := by
  set 𝔰 : ℝ := PrimeGaps.singularSeries S.γ with h𝔰
  set τ : ℝ := (#S.V.divisors : ℝ) with hτ
  set PLS : ℝ := ellV S.V with hPLS
  have hzpow : 0 ≤ z ^ (-(1 : ℝ) / 8) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h𝔰pos : 0 < 𝔰 := PrimeGaps.singularSeries_pos S
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast S.V_pos
  have hτnn : 0 ≤ τ := by rw [hτ]; positivity
  set t : ℝ := ((⌈z⌉₊ + 1 : ℕ) : ℝ) with htdef
  have hzc : z ≤ (⌈z⌉₊ : ℝ) := Nat.le_ceil z
  have hceil_lt : (⌈z⌉₊ : ℝ) < z + 1 := Nat.ceil_lt_add_one (by linarith)
  have ht2 : (2 : ℝ) ≤ t := by rw [htdef]; push_cast; linarith
  have htpos : (0 : ℝ) < t := by linarith
  have ht1 : (1 : ℝ) ≤ t := by linarith
  have hBeq : ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d = S.H t := by
    unfold SieveDatum.H
    rw [htdef, Nat.ceil_natCast, Finset.sum_filter]
    refine Finset.sum_congr rfl fun d hd ↦ ?_
    rw [Finset.mem_range] at hd
    rcases Nat.eq_zero_or_pos d with rfl | hd0
    · rw [if_neg (by simp), sieveDatum_h_zero]
    · rw [if_pos ⟨hd0, by exact_mod_cast hd⟩]
  have hHb := hHasymp t ht2
  rw [abs_le] at hHb
  have htz2 : t ≤ z ^ 2 := by
    have hfac : (0 : ℝ) ≤ (z - 2) * (z + 1) := mul_nonneg (by linarith) (by linarith)
    rw [htdef]; push_cast; linarith only [hceil_lt, hz, hfac]
  have hHle : S.H t ≤ 𝔰 * Real.log t + ch₁ * 𝔰 * (1 + PLS) +
      ch₂ * τ * t ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * t) := by
    rw [h𝔰, hPLS, hτ]; linarith only [hHb.2]
  have hlogt : Real.log t ≤ 2 * Real.log z :=
    calc Real.log t ≤ Real.log (z ^ 2) := Real.log_le_log htpos htz2
      _ = 2 * Real.log z := by rw [Real.log_pow]; push_cast; ring
  have htpow' : t ^ (-(1 : ℝ) / 8) ≤ z ^ (-(1 : ℝ) / 8) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) (by rw [htdef]; push_cast; linarith) (by norm_num)
  have hVt : (1 : ℝ) ≤ 2 * (S.V : ℝ) * t := by nlinarith
  have hlog2Vt_nn : 0 ≤ Real.log (2 * S.V * t) := Real.log_nonneg hVt
  have hlog2Vt_le : Real.log (2 * S.V * t) ≤ Real.log (2 * S.V * z) + Real.log z :=
    calc Real.log (2 * S.V * t) ≤ Real.log ((2 * (S.V : ℝ) * z) * z) :=
          Real.log_le_log (by linarith) (by nlinarith)
      _ = Real.log (2 * S.V * z) + Real.log z := by
          rw [Real.log_mul (by positivity) (by linarith)]
  have hterm : ch₂ * τ * t ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * t) ≤
      ch₂ * τ * (z ^ (-(1 : ℝ) / 8) * (Real.log (2 * S.V * z) + Real.log z)) := by
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hch₂ hτnn)
    exact (mul_le_mul_of_nonneg_right htpow' hlog2Vt_nn).trans
      (mul_le_mul_of_nonneg_left hlog2Vt_le hzpow)
  rw [hBeq]
  linarith only [hHle, hterm, mul_le_mul_of_nonneg_left hlogt h𝔰pos.le]

/-- **One telescoping layer of the iterated partial summation.**  If `PE` bounds the
partial-summation discrepancy of every single prefix `u`, and `Bc` bounds both the truncated
weight sum `∑_{d ≤ ⌈z⌉₊} S.h d` and the main term `𝔖 log z`, then consecutive `sieveE` layers
differ by at most `Bc ^ (n - 1) * PE`. -/
private theorem sieveE_layer_step_le {n : ℕ} (S : SieveDatum)
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hsupp : Function.support F ⊆ 𝓡 n) (z : ℝ) (hz : 2 ≤ z) (Bc PE : ℝ)
    (hBcnn : 0 ≤ Bc) (hPEnn : 0 ≤ PE)
    (hBsum_le : ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d ≤ Bc)
    (h𝔰logz_le_Bc : PrimeGaps.singularSeries S.γ * Real.log z ≤ Bc)
    (m : ℕ) (hm : m < n)
    (hperprefix : ∀ u : Fin m → ℕ,
      |(∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
            S.h d * layerG z F u (Real.log ↑d / Real.log z)) -
        PrimeGaps.singularSeries S.γ * Real.log z * ∫ s in (0 : ℝ)..1, layerG z F u s| ≤ PE) :
    |sieveE S z F (m + 1) - sieveE S z F m| ≤ Bc ^ (n - 1) * PE := by
  classical
  set 𝔰 : ℝ := PrimeGaps.singularSeries S.γ with h𝔰
  have hz1 : (1 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have h𝔰pos : 0 < 𝔰 := PrimeGaps.singularSeries_pos S
  have hh_nonneg : ∀ d, 0 ≤ S.h d := S.h_nonneg
  set Bsum : ℝ := ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d with hBsumdef
  have hBsum_nonneg : 0 ≤ Bsum := by
    rw [hBsumdef]; exact Finset.sum_nonneg (fun d _ ↦ hh_nonneg d)
  rw [sieveE_layer_identity S z F hF hsupp m hm hz]
  set wt : (Fin m → ℕ) → ℝ := fun u ↦ (if (∀ i, 1 ≤ u i) then (∏ i, S.h (u i)) else 0) with hwt
  set Td : (Fin m → ℕ) → ℝ := fun u ↦ ∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
        S.h d * layerG z F u (Real.log ↑d / Real.log z) with hTd
  set Ig : (Fin m → ℕ) → ℝ := fun u ↦ 𝔰 * Real.log z * ∫ s in (0 : ℝ)..1, layerG z F u s with hIg
  set box : Finset (Fin m → ℕ) :=
    Fintype.piFinset (fun _ : Fin m ↦ Finset.range (⌈z⌉₊ + 1)) with hbox
  have hwt_nn : ∀ u, 0 ≤ wt u := by
    intro u; simp only [hwt]; split
    · exact Finset.prod_nonneg fun i _ ↦ hh_nonneg (u i)
    · exact le_rfl
  have hvanish : ∀ u ∉ box, wt u * (Td u - Ig u) = 0 := by
    intro u hu
    rw [hbox] at hu
    have hlayer0 := layerG_eq_zero_of_notMem_box z hz F hsupp hm u hu
    simp [hTd, hIg, hlayer0]
  have htsum_eq : (∑' u : Fin m → ℕ, wt u * (Td u - Ig u)) =
      ∑ u ∈ box, wt u * (Td u - Ig u) := tsum_eq_sum (fun u hu ↦ hvanish u hu)
  rw [abs_mul, abs_of_nonneg (pow_nonneg (mul_nonneg h𝔰pos.le hlogz.le) _), htsum_eq]
  have hboxbound : |∑ u ∈ box, wt u * (Td u - Ig u)| ≤ Bsum ^ m * PE := by
    have hfactor : ∑ u ∈ box, wt u * PE = Bsum ^ m * PE := by
      rw [← Finset.sum_mul]
      congr 1
      rw [hbox]
      simp only [hwt]
      rw [sieveDatum_boxsum_eq S z, ← hBsumdef]
    calc |∑ u ∈ box, wt u * (Td u - Ig u)|
        ≤ ∑ u ∈ box, |wt u * (Td u - Ig u)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ u ∈ box, wt u * |Td u - Ig u| :=
          Finset.sum_congr rfl fun u _ ↦ by rw [abs_mul, abs_of_nonneg (hwt_nn u)]
      _ ≤ ∑ u ∈ box, wt u * PE :=
          Finset.sum_le_sum fun u _ ↦ mul_le_mul_of_nonneg_left (hperprefix u) (hwt_nn u)
      _ = Bsum ^ m * PE := hfactor
  have hpowbase : (𝔰 * Real.log z) ^ (n - m - 1) * Bsum ^ m ≤ Bc ^ (n - 1) := by
    have hexp : (n - m - 1) + m = n - 1 := by omega
    calc (𝔰 * Real.log z) ^ (n - m - 1) * Bsum ^ m ≤ Bc ^ (n - m - 1) * Bc ^ m :=
          mul_le_mul (pow_le_pow_left₀ (mul_nonneg h𝔰pos.le hlogz.le) h𝔰logz_le_Bc _)
            (pow_le_pow_left₀ hBsum_nonneg hBsum_le _) (pow_nonneg hBsum_nonneg _)
            (pow_nonneg hBcnn _)
      _ = Bc ^ (n - 1) := by rw [← pow_add, hexp]
  calc (𝔰 * Real.log z) ^ (n - m - 1) * |∑ u ∈ box, wt u * (Td u - Ig u)|
      ≤ (𝔰 * Real.log z) ^ (n - m - 1) * (Bsum ^ m * PE) :=
        mul_le_mul_of_nonneg_left hboxbound (pow_nonneg (mul_nonneg h𝔰pos.le hlogz.le) _)
    _ = ((𝔰 * Real.log z) ^ (n - m - 1) * Bsum ^ m) * PE := by ring
    _ ≤ Bc ^ (n - 1) * PE := mul_le_mul_of_nonneg_right hpowbase hPEnn

-- For a sieve datum `S`, smooth `F` supported on `𝓡 n`, and `z ≥ 2`, the difference between
-- `sieveE S z F n` and `sieveE S z F 0` satisfies the stated bound.
/-- Bound for `|sieveE S z F n - sieveE S z F 0|`, obtained by peeling the `n` coordinates one at a
time and applying `S1_partial_sum_sharp` to each layer. -/
theorem sieveDatum_kfold_partial_sum : ∃ Cs₁ Cs₂ Ch₁ Ch₂ : ℝ → ℝ → ℝ,
      (∀ A₁ A₃ : ℝ, 0 < Cs₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < Cs₂ A₁ A₃) ∧
        (∀ A₁ A₃ : ℝ, 0 < Ch₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 < Ch₂ A₁ A₃) ∧
      ∀ {n : ℕ} (S : SieveDatum) (F : EuclideanSpace ℝ (Fin n) → ℝ),
        ContDiff ℝ (⊤ : ℕ∞) F → Function.support F ⊆ 𝓡 n → ∀ z : ℝ, 2 ≤ z →
          |sieveE S z F n - sieveE S z F 0| ≤ (n : ℝ) *
              (2 * PrimeGaps.singularSeries S.γ * Real.log z +
                  Ch₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
                  Ch₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                      (z ^ (-(1 : ℝ) / 8) * (Real.log (2 * S.V * z) + Real.log z))) ^ (n - 1) *
              (2 * (3 * MaynardSmoothY.Fmax F ^ 2) *
                  (2 * Cs₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
                      Cs₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) *
                          (z ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * z) +
                              (8 * Real.log (2 * S.V) + 64) / Real.log z))) := by
  classical
  obtain ⟨Cs₁, Cs₂, hCs₁, hCs₂, hsharp⟩ := S1_partial_sum_sharp
  obtain ⟨Ch₁, Ch₂, hCh₁, hCh₂, hHasymp⟩ := PrimeGaps.slem_H_error_assembly
  refine ⟨Cs₁, Cs₂, Ch₁, Ch₂, hCs₁, hCs₂, hCh₁, hCh₂, ?_⟩
  intro n S F hF hsupp z hz
  set 𝔰 : ℝ := PrimeGaps.singularSeries S.γ with h𝔰
  set τ : ℝ := (#S.V.divisors : ℝ) with hτ
  set Fm : ℝ := MaynardSmoothY.Fmax F ^ 2 with hFm
  set PLS : ℝ := ellV S.V with hPLS
  have hz1 : (1 : ℝ) < z := by linarith
  have hlogz : 0 < Real.log z := Real.log_pos hz1
  have hzpow : 0 ≤ z ^ (-(1 : ℝ) / 8) := (Real.rpow_pos_of_pos (by linarith) _).le
  have h𝔰pos : 0 < 𝔰 := PrimeGaps.singularSeries_pos S
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast S.V_pos
  have hτnn : 0 ≤ τ := by rw [hτ]; positivity
  have hFmnn : 0 ≤ Fm := by rw [hFm]; positivity
  have hPLSnn : 0 ≤ PLS := by rw [hPLS]; exact ellV_nonneg S.V
  have hlog2Vz : 0 ≤ Real.log (2 * S.V * z) := by
    apply Real.log_nonneg
    exact one_le_mul_of_one_le_of_one_le (by linarith only [hV1]) (by linarith only [hz])
  have hlog2V : 0 ≤ Real.log (2 * S.V) := by apply Real.log_nonneg; linarith only [hV1]
  set PE : ℝ := 2 * (3 * Fm) * (2 * Cs₁ S.A₁ S.A₃ * 𝔰 * (1 + PLS) +
          Cs₂ S.A₁ S.A₃ * τ * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * z) +
              (8 * Real.log (2 * S.V) + 64) / Real.log z)) with hPEdef
  set Bc : ℝ := 2 * 𝔰 * Real.log z + Ch₁ S.A₁ S.A₃ * 𝔰 * (1 + PLS) +
      Ch₂ S.A₁ S.A₃ * τ * (z ^ (-(1 : ℝ) / 8) * (Real.log (2 * S.V * z) + Real.log z)) with hBcdef
  have hPEnn : 0 ≤ PE := by
    have hc1 : 0 ≤ Cs₁ S.A₁ S.A₃ := (hCs₁ S.A₁ S.A₃).le
    have hc2 : 0 ≤ Cs₂ S.A₁ S.A₃ := (hCs₂ S.A₁ S.A₃).le
    have hin : 0 ≤ z ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * z) +
        (8 * Real.log (2 * S.V) + 64) / Real.log z :=
      add_nonneg (mul_nonneg hzpow hlog2Vz) (div_nonneg (by linarith) hlogz.le)
    have hsum : 0 ≤ 2 * Cs₁ S.A₁ S.A₃ * 𝔰 * (1 + PLS) +
        Cs₂ S.A₁ S.A₃ * τ * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * S.V * z) +
            (8 * Real.log (2 * S.V) + 64) / Real.log z) := by positivity
    rw [hPEdef]; positivity
  have h𝔰logz_le_Bc : 𝔰 * Real.log z ≤ Bc := by
    have hin : 0 ≤ z ^ (-(1 : ℝ) / 8) * (Real.log (2 * S.V * z) + Real.log z) :=
      mul_nonneg hzpow (by linarith)
    have t1 : 0 ≤ Ch₁ S.A₁ S.A₃ * 𝔰 * (1 + PLS) :=
      mul_nonneg (mul_nonneg (hCh₁ S.A₁ S.A₃).le h𝔰pos.le) (by linarith)
    have t2 : 0 ≤ Ch₂ S.A₁ S.A₃ * τ * (z ^ (-(1 : ℝ) / 8) * (Real.log (2 * S.V * z) +
      Real.log z)) :=
      mul_nonneg (mul_nonneg (hCh₂ S.A₁ S.A₃).le hτnn) hin
    rw [hBcdef]
    linarith only [mul_nonneg h𝔰pos.le hlogz.le, t1, t2]
  have hBcnn : 0 ≤ Bc := le_trans (mul_nonneg h𝔰pos.le hlogz.le) h𝔰logz_le_Bc
  have hBsum_le : ∑ d ∈ Finset.range (⌈z⌉₊ + 1), S.h d ≤ Bc :=
    sum_h_range_ceil_succ_le S z hz (Ch₁ S.A₁ S.A₃) (Ch₂ S.A₁ S.A₃)
      (hCh₂ S.A₁ S.A₃).le (fun t ht ↦ hHasymp S t ht)
  have hperprefix : ∀ (m : ℕ), m < n → ∀ u : Fin m → ℕ,
      |(∑ d ∈ Finset.range ⌈z⌉₊ with (0 : ℕ) < d ∧ (↑d : ℝ) < z,
            S.h d * layerG z F u (Real.log ↑d / Real.log z)) -
        𝔰 * Real.log z * ∫ s in (0 : ℝ)..1, layerG z F u s| ≤ PE := by
    intro m hm u
    have hbdd_lip := S1_layerG_bdd_lip hm z F hF hsupp u
    have hMnn : (0 : ℝ) ≤ 3 * Fm := by rw [hFm]; positivity
    have hGbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |layerG z F u x| ≤ 3 * Fm := fun x hx ↦ by
      rw [hFm]; linarith only [hbdd_lip.1 x hx, sq_nonneg (MaynardSmoothY.Fmax F)]
    have hGlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1,
        |layerG z F u x - layerG z F u y| ≤ (3 * Fm) * |x - y| := by
      rw [hFm]; exact hbdd_lip.2
    rw [hPEdef, h𝔰, hPLS, hτ]
    exact hsharp S (layerG z F u) (3 * Fm) hMnn hGbdd hGlip z hz
  have hstep : ∀ (m : ℕ), m < n →
      |sieveE S z F (m + 1) - sieveE S z F m| ≤ Bc ^ (n - 1) * PE := fun m hm ↦
    sieveE_layer_step_le S F hF hsupp z hz Bc PE hBcnn hPEnn hBsum_le h𝔰logz_le_Bc m hm
      (hperprefix m hm)
  rw [← Finset.sum_range_sub (fun m ↦ sieveE S z F m)]
  calc |∑ m ∈ Finset.range n, (sieveE S z F (m + 1) - sieveE S z F m)|
      ≤ ∑ m ∈ Finset.range n, |sieveE S z F (m + 1) - sieveE S z F m| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ ∈ Finset.range n, Bc ^ (n - 1) * PE :=
        Finset.sum_le_sum fun m hm ↦ hstep m (Finset.mem_range.mp hm)
    _ = (n : ℝ) * Bc ^ (n - 1) * PE := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring

/-- For per-coordinate weights `g i: ℕ → ℝ` each finitely supported (`g i n ≠ 0 → n ≤ M`), the
pi-tsum of the product over the coordinates `≠ m` (with coordinate `m` pinned to the value `1` via
the guard) factorizes as the product of the single-coordinate tsums over `i ≠ m`:
`∑'_ρ [ρ m = 1] · ∏_{i≠m} g i (ρ i) = ∏_{i≠m} ∑'_n g i n`.
-/
theorem tsum_pin_coord_prod {k : ℕ} (M : ℕ) (m : Fin k) (g : Fin k → ℕ → ℝ)
    (hsupp : ∀ i n, g i n ≠ 0 → n ≤ M) :
    (∑' ρ : Fin k → ℕ, if ρ m = 1 then ∏ i ∈ Finset.univ.erase m, g i (ρ i) else 0) =
      ∏ i ∈ Finset.univ.erase m, ∑' n : ℕ, g i n := by
  classical
  set g' : Fin k → ℕ → ℝ := fun i n ↦
    if i = m then (if n = 1 then (1 : ℝ) else 0) else g i n with hg'
  have hsupp' : ∀ i n, g' i n ≠ 0 → n ≤ max 1 M := by
    intro i n hne
    by_cases him : i = m
    · simp only [hg', if_pos him] at hne
      rcases eq_or_ne n 1 with rfl | hn1
      · exact le_max_left 1 M
      · simp [hn1] at hne
    · exact (hsupp i n (by simpa only [hg', if_neg him] using hne)).trans (le_max_right 1 M)
  have hpin : ∀ ρ : Fin k → ℕ,
      (if ρ m = 1 then ∏ i ∈ Finset.univ.erase m, g i (ρ i) else 0) = ∏ i, g' i (ρ i) := by
    intro ρ
    rw [← Finset.prod_erase_mul Finset.univ (fun i ↦ g' i (ρ i)) (Finset.mem_univ m)]
    have hgm : g' m (ρ m) = (if ρ m = 1 then (1 : ℝ) else 0) := by
      simp only [hg', if_pos rfl]
    have hgi : ∀ i ∈ Finset.univ.erase m, g' i (ρ i) = g i (ρ i) := fun i hi ↦ by
      rw [Finset.mem_erase] at hi; simp only [hg', if_neg hi.1]
    rw [Finset.prod_congr rfl hgi, hgm]
    by_cases h1 : ρ m = 1 <;> simp [h1]
  rw [tsum_congr hpin, SijD0.tsum_prod_of_box (max 1 M) g' hsupp',
    ← Finset.prod_erase_mul Finset.univ (fun i ↦ ∑' n : ℕ, g' i n) (Finset.mem_univ m)]
  have hmfac : (∑' n : ℕ, g' m n) = 1 := by
    simp only [hg', if_pos rfl]
    rw [tsum_eq_single 1 fun b hb ↦ by simp [hb]]; simp
  rw [hmfac, mul_one]
  refine Finset.prod_congr rfl fun i hi ↦ ?_
  rw [Finset.mem_erase] at hi
  simp only [hg', if_neg hi.1]

end PrimeGaps
