/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import Mathlib.MeasureTheory.Order.Group.Lattice
public import PrimeGapsTheory.Arithmetic.DivisorTails
public import PrimeGapsTheory.Arithmetic.GammaDensity
public import PrimeGapsTheory.Sieve.Common.SieveDatumEval

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Partial summation in a g-weighted coordinate

Estimates the one-dimensional partial sum with the Maynard g-weight.

## Main results

* `sharp_partial_sum`: Partial summation of `S.h` against a `C¹` test function.
* `sum_h_eq_muSq_g`: The Maynard datum's `h`-weight is `μ²/g` on integers coprime to `W N`.
* `lem_S2m_g_coord`: Approximates the g-weighted coordinate sum by its integral main term.
-/

@[expose] public section

open scoped ArithmeticFunction.Moebius
open scoped ArithmeticFunction.detotient
open scoped Finset

namespace PrimeGaps

/-- Partial summation against a `C¹` test function: `∑_{0 < d < z} S.h d * G (log d / log z)`
differs from `𝔖(S.γ) * log z * ∫₀¹ G` by an explicit error in `ellV S.V`, `τ(S.V)`, `z ^ (-1/8)`
and `1 / log z`, with constants depending only on `S.A₁` and `S.A₃`. -/
theorem sharp_partial_sum : ∃ C₁ C₂ C₃ : ℝ → ℝ → ℝ,
      (∀ A₁ A₃ : ℝ, 0 ≤ C₁ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 ≤ C₂ A₁ A₃) ∧ (∀ A₁ A₃ : ℝ, 0 ≤ C₃ A₁ A₃) ∧
      ∀ (S : SieveDatum) (G : ℝ → ℝ), ContDiff ℝ 1 G → ∀ (z : ℝ), 2 ≤ z →
        |(∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (d : ℝ) < z),
              S.h d * G (Real.log d / Real.log z)) -
            PrimeGaps.singularSeries S.γ * Real.log z * ∫ x in (0 : ℝ)..1, G x| ≤
          C₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) * Gmax G +
            C₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * z ^ ((-1 : ℝ) / 8) *
                Real.log (2 * (S.V : ℝ) * z) * Gmax G +
            C₃ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * Real.log (2 * (S.V : ℝ)) /
                Real.log z * Gmax G := by
  obtain ⟨D₁, D₂, hD₁pos, hD₂pos, hSharp⟩ := S1_partial_sum_sharp
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 8 + 64 / Real.log 2 with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  refine ⟨fun A₁ A₃ ↦ 4 * D₁ A₁ A₃, fun A₁ A₃ ↦ 2 * D₂ A₁ A₃,
    fun A₁ A₃ ↦ 2 * D₂ A₁ A₃ * K, ?_, ?_, ?_, ?_⟩
  · exact fun A₁ A₃ ↦ mul_nonneg (by norm_num) (hD₁pos A₁ A₃).le
  · exact fun A₁ A₃ ↦ mul_nonneg (by norm_num) (hD₂pos A₁ A₃).le
  · exact fun A₁ A₃ ↦ mul_nonneg (mul_nonneg (by norm_num) (hD₂pos A₁ A₃).le) hKnn
  intro S G hG z hz
  have hM : 0 ≤ Gmax G := le_trans (abs_nonneg _)
      (Gmax_bounds G hG (Set.mem_Icc.mpr ⟨le_refl (0 : ℝ), zero_le_one⟩)).1
  have hbdd : ∀ x ∈ Set.Icc (0 : ℝ) 1, |G x| ≤ Gmax G := fun x hx ↦ (Gmax_bounds G hG hx).1
  have hlip : ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |G x - G y| ≤ Gmax G * |x - y| := by
    intro x hx y hy
    have hdiff : ∀ w ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ G w :=
      fun w _ ↦ (hG.differentiable (by norm_num)).differentiableAt
    have hbound : ∀ w ∈ Set.Icc (0 : ℝ) 1, ‖deriv G w‖ ≤ Gmax G := fun w hw ↦ by
      simpa only [Real.norm_eq_abs] using (Gmax_bounds G hG hw).2
    have h := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_deriv_le hdiff hbound hy hx
    rwa [Real.norm_eq_abs, Real.norm_eq_abs] at h
  have hmain := hSharp S G (Gmax G) hM hbdd hlip z hz
  refine le_trans hmain ?_
  have hVpos : 0 < S.V := S.V_pos
  have hV1 : (1 : ℝ) ≤ (S.V : ℝ) := by exact_mod_cast hVpos
  have hz1 : (1 : ℝ) < z := by linarith
  have hlogz_pos : 0 < Real.log z := Real.log_pos hz1
  have hτ_nonneg : 0 ≤ (#S.V.divisors : ℝ) := by positivity
  have hDτ : 0 ≤ D₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) := mul_nonneg (hD₂pos _ _).le hτ_nonneg
  have h2G : 0 ≤ 2 * Gmax G := by linarith
  have hlog2_le : Real.log 2 ≤ Real.log (2 * (S.V : ℝ)) :=
    Real.log_le_log (by norm_num) (by nlinarith [hV1])
  have hnumK : 8 * Real.log (2 * (S.V : ℝ)) + 64 ≤ K * Real.log (2 * (S.V : ℝ)) := by
    have h64 : (64 : ℝ) ≤ 64 / Real.log 2 * Real.log (2 * (S.V : ℝ)) := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]; nlinarith [hlog2_le]
    rw [hKdef]; nlinarith [h64]
  have hFbound : (8 * Real.log (2 * (S.V : ℝ)) + 64) / Real.log z ≤
      K * Real.log (2 * (S.V : ℝ)) / Real.log z := by
    simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_right hnumK (inv_pos.mpr hlogz_pos).le
  calc (2 * Gmax G) * (2 * D₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
            D₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z) +
                    (8 * Real.log (2 * ↑S.V) + 64) / Real.log z)) ≤ (2 * Gmax G) *
          (2 * D₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) +
            D₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * (z ^ (-(1 : ℝ) / 8) * Real.log (2 * ↑S.V * z) +
                    K * Real.log (2 * ↑S.V) / Real.log z)) :=
        mul_le_mul_of_nonneg_left
          (add_le_add le_rfl (mul_le_mul_of_nonneg_left (add_le_add le_rfl hFbound) hDτ)) h2G
    _ = 4 * D₁ S.A₁ S.A₃ * PrimeGaps.singularSeries S.γ * (1 + ellV S.V) * Gmax G +
          2 * D₂ S.A₁ S.A₃ * (#S.V.divisors : ℝ) * z ^ ((-1 : ℝ) / 8) *
              Real.log (2 * (S.V : ℝ) * z) * Gmax G +
          2 * D₂ S.A₁ S.A₃ * K * (#S.V.divisors : ℝ) * Real.log (2 * (S.V : ℝ)) /
              Real.log z * Gmax G := by ring

open scoped PrimeGaps.sieveModulus in
/-- The `h` -weighted sum of the Maynard sieve datum is
`∑_{0 < r < z, (r, W N) = 1} μ(r)² / g(r) * G (log r / log z)`. -/
theorem sum_h_eq_muSq_g (N : ℕ) (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ)) (G : ℝ → ℝ) (z : ℝ) :
    (∑ d ∈ (Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (↑d : ℝ) < z),
        (maynardSieveDatum N hN hD).h d * G (Real.log ↑d / Real.log z))
      =
    (∑ r ∈ (Finset.range ⌈z⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < z ∧ Nat.Coprime r (W N)),
        (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log z)) := by
  have hbase : ((Finset.range ⌈z⌉₊).filter
          (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < z ∧ Nat.Coprime r (W N))) =
        ((Finset.range ⌈z⌉₊).filter (fun d : ℕ ↦ 0 < d ∧ (↑d : ℝ) < z)).filter
            (fun r : ℕ ↦ Nat.Coprime r (W N)) := by
    rw [Finset.filter_filter]
    exact Finset.filter_congr fun x _ ↦ and_assoc.symm
  rw [hbase]
  conv_rhs => rw [Finset.sum_filter]
  refine Finset.sum_congr rfl fun d _ ↦ ?_
  have hh : (maynardSieveDatum N hN hD).h d =
      (μ d : ℝ) ^ 2 * (maynardSieveDatum N hN hD).gStar d := rfl
  rw [hh]
  by_cases hcop : Nat.Coprime d (W N)
  · rw [if_pos hcop]
    by_cases hsf : Squarefree d
    · rw [maynardSieveDatum_gStar_squarefree_coprime N hN hD d hsf hcop]
      have hmu : (μ d : ℝ) ^ 2 = 1 := by
        exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
      rw [hmu]; ring
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; push_cast; ring
  · rw [if_neg hcop]
    by_cases hsf : Squarefree d
    · rw [maynardSieveDatum_gStar_not_coprime N hN hD d hsf hcop]
      ring
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]; push_cast; ring

open scoped PrimeGaps.sieveModulus in
/-- `|𝔖(γ) - φ(W N) / W N| ≤ C * (φ(W N) / W N) * (1 / D₀ N)` for the Maynard datum's density and
all large `N`. -/
theorem singularSeries_maynard_asymptotic : ∃ C : ℝ, 0 < C ∧ ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) →
      ∀ (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
        |PrimeGaps.singularSeries (maynardSieveDatum N hN hD).γ - ((W N).totient : ℝ) / (W N : ℝ)| ≤
          C * (((W N).totient : ℝ) / (W N : ℝ)) *
              (1 / PrimeGaps.D₀ (N : ℝ)) := by
  exact singularSeries_maynardSieveDatum_γ_asymptotic

/-- A natural number bounded by `L ^ 2` has at most `L ^ 2` divisors, so `τ(V) ^ 2 ≤ L ^ 4`. -/
theorem card_divisors_sq_le_pow_four {V : ℕ} {L : ℝ} (hV : (V : ℝ) ≤ L ^ 2) :
    (#V.divisors : ℝ) ^ 2 ≤ L ^ 4 := by
  have hcard : (#V.divisors : ℝ) ≤ (V : ℝ) := by
    exact_mod_cast Nat.card_divisors_le_self V
  exact (pow_le_pow_left₀ (by positivity) (hcard.trans hV) 2).trans_eq (by ring)

/-- For a natural number `V ≤ L ^ 2` with `1 ≤ L`, the logarithm `log (2 * V)` is at most `3 * L`:
it is at most `log 2 + 2 * log L`, and both `log 2` and `log L` are at most `L`. -/
theorem log_two_mul_le_three_mul {V : ℕ} {L : ℝ} (hL : 1 ≤ L) (hV : (V : ℝ) ≤ L ^ 2) :
    Real.log (2 * (V : ℝ)) ≤ 3 * L := by
  have hLpos : 0 < L := by linarith
  have hlog2L : Real.log 2 ≤ L := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hlogL : Real.log L ≤ L := by linarith [Real.log_le_sub_one_of_pos hLpos]
  rcases Nat.eq_zero_or_pos V with rfl | hVpos
  · simp only [Nat.cast_zero, mul_zero, Real.log_zero]
    linarith
  · have : (0 : ℝ) < (V : ℝ) := by exact_mod_cast hVpos
    calc Real.log (2 * (V : ℝ)) ≤ Real.log (2 * L ^ 2) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 2 + 2 * Real.log L := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ 3 * L := by linarith

open Filter Asymptotics in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `τ(W N) ^ 2 * log (2 * W N) ≤ log R` for all large `N`. -/
theorem tau_sq_log_le_logR (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) → (#(W N).divisors : ℝ) ^ 2 * Real.log (2 *
        ((W N : ℝ))) ≤
        Real.log (R) := by
  set κ : ℝ := θ / 2 - δ with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith [hδ.2]
  have hcore : ∀ᶠ x : ℝ in Filter.atTop, 3 * (Real.log x) ^ 5 ≤ κ * x := by
    filter_upwards [Real.eventually_log_pow_le_const_mul 5
      (show (0 : ℝ) < κ / 3 by positivity)] with x hx
    linarith
  have hcompN : ∀ᶠ N : ℕ in Filter.atTop,
      3 * (Real.log (Real.log (N : ℝ))) ^ 5 ≤ κ * Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually hcore
  have hLLge : ∀ᶠ N : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (Real.log (N : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 1)
  have hNpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < N := Filter.eventually_gt_atTop 0
  have hWsize := PrimeGaps.lem_W_size
  have hall : ∀ᶠ N : ℕ in Filter.atTop, (#(W N).divisors : ℝ) ^ 2 * Real.log (2 *
        ((W N : ℝ))) ≤
        Real.log (R) := by
    filter_upwards [hWsize, hcompN, hLLge, hNpos]
      with N hW hcomp hLL hNpos
    have hReq : Real.log (R) = κ * Real.log (N : ℝ) :=
      Real.log_rpow (by exact_mod_cast hNpos) κ
    rw [hReq]
    set LL : ℝ := Real.log (Real.log (N : ℝ)) with hLLdef
    have hLLpos : 0 < LL := by linarith
    have hWnn : (1 : ℝ) ≤ (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos (N := N)
    have hlog2Wnn : 0 ≤ Real.log (2 * (W N : ℝ)) := Real.log_nonneg (by linarith)
    calc (#(W N).divisors : ℝ) ^ 2 * Real.log (2 * (W N : ℝ)) ≤ LL ^ 4 * (3 * LL) :=
          mul_le_mul (card_divisors_sq_le_pow_four hW) (log_two_mul_le_three_mul hLL hW)
            hlog2Wnn (by positivity)
      _ = 3 * LL ^ 5 := by ring
      _ ≤ κ * Real.log (N : ℝ) := hcomp
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hall
  exact ⟨(a : ℝ), fun N hN ↦ ha N (by exact_mod_cast hN)⟩

open Filter Asymptotics in
open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `τ(W N) ^ 2 * R ^ (-1/8) * log (2 * W N * R) ≤ log 2` for all large `N`. -/
theorem tau_sq_rpow_log_le_log2 (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) → (#(W N).divisors : ℝ) ^ 2 * (R) ^ ((-1 : ℝ) /
        8) * Real.log (2 * ((W N : ℝ)) * R) ≤
            Real.log 2 := by
  set κ : ℝ := θ / 2 - δ with hκdef
  have hκ : 0 < κ := by rw [hκdef]; linarith [hδ.2]
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set K : ℝ := 3 + κ with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hcore : ∀ᶠ x : ℝ in Filter.atTop, (Real.log x) ^ 5 * x ^ ((-κ) / 8) ≤ Real.log 2 / K := by
    have hlo : (fun x ↦ Real.log x ^ (5 : ℝ)) =o[Filter.atTop] (fun x ↦ x ^ (κ / 8)) :=
      isLittleO_log_rpow_rpow_atTop 5 (by positivity)
    have hb := (Asymptotics.isLittleO_iff.mp hlo)
      (show (0 : ℝ) < Real.log 2 / K by positivity)
    have hev : ∀ᶠ x : ℝ in Filter.atTop, (1 : ℝ) ≤ x := Filter.eventually_ge_atTop 1
    filter_upwards [hb, hev] with x hx hx1
    have hxpos : 0 < x := by linarith
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hxpos (κ / 8))] at hx
    have hlogeq : Real.log x ^ (5 : ℝ) = (Real.log x) ^ (5 : ℕ) := by
      rw [← Real.rpow_natCast (Real.log x) 5]; norm_num
    rw [hlogeq] at hx
    have hle : (Real.log x) ^ 5 ≤ (Real.log 2 / K) * x ^ (κ / 8) := le_trans (le_abs_self _) hx
    have hxs : 0 < x ^ (κ / 8) := Real.rpow_pos_of_pos hxpos (κ / 8)
    have hneg : x ^ ((-κ) / 8) = (x ^ (κ / 8))⁻¹ := by
      rw [show (-κ) / 8 = -(κ / 8) by ring, Real.rpow_neg hxpos.le]
    rw [hneg, ← div_eq_mul_inv, div_le_iff₀ hxs]
    linarith [hle]
  have hcompN : ∀ᶠ N : ℕ in Filter.atTop,
      (Real.log (N : ℝ)) ^ 5 * (N : ℝ) ^ ((-κ) / 8) ≤ Real.log 2 / K :=
    tendsto_natCast_atTop_atTop.eventually hcore
  have hLLge : ∀ᶠ N : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (Real.log (N : ℝ)) :=
    ((Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp
      tendsto_natCast_atTop_atTop).eventually (Filter.eventually_ge_atTop 1)
  have hlogNge : ∀ᶠ N : ℕ in Filter.atTop, (1 : ℝ) ≤ Real.log (N : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
      (Filter.eventually_ge_atTop 1)
  have hNpos : ∀ᶠ N : ℕ in Filter.atTop, 0 < N := Filter.eventually_gt_atTop 0
  have hWsize := PrimeGaps.lem_W_size
  have hall : ∀ᶠ N : ℕ in Filter.atTop, (#(W N).divisors : ℝ) ^ 2 * (R) ^ ((-1 : ℝ) /
        8) * Real.log (2 * ((W N : ℝ)) * R) ≤
            Real.log 2 := by
    filter_upwards [hWsize, hcompN, hLLge, hlogNge, hNpos]
      with N hW hcomp hLL hlogN hNpos
    have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hNpos
    have hRdef : R = (N : ℝ) ^ κ := rfl
    have hRpos : 0 < R := hRdef ▸ Real.rpow_pos_of_pos hNr κ
    have hRexp : (R) ^ ((-1 : ℝ) / 8) = (N : ℝ) ^ ((-κ) / 8) := by
      rw [hRdef, ← Real.rpow_mul hNr.le]
      congr 1; ring
    have hNge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hNpos
    have hR1 : (1 : ℝ) ≤ R := hRdef ▸ Real.one_le_rpow hNge1 hκ.le
    set LL : ℝ := Real.log (Real.log (N : ℝ)) with hLLdef
    have hLLpos : 0 < LL := by linarith
    set LN : ℝ := Real.log (N : ℝ) with hLNdef
    have hLNpos : 0 < LN := by linarith
    have hWnn : (1 : ℝ) ≤ (W N : ℝ) := by exact_mod_cast PrimeGaps.W_pos (N := N)
    have hLLleLN : LL ≤ LN := by
      rw [hLLdef, hLNdef]
      linarith [Real.log_le_sub_one_of_pos hLNpos]
    have hcard2LN : (#(W N).divisors : ℝ) ^ 2 ≤ LN ^ 4 :=
      card_divisors_sq_le_pow_four (hW.trans (pow_le_pow_left₀ hLLpos.le hLLleLN 2))
    have hlog2WR : Real.log (2 * ((W N : ℝ)) * R) ≤ K * LN := by
      rw [Real.log_mul (by positivity) hRpos.ne', hRdef, Real.log_rpow hNr, hKdef]
      nlinarith [log_two_mul_le_three_mul hLL hW, hLLleLN, hLNpos]
    have hlog2WRnn : 0 ≤ Real.log (2 * ((W N : ℝ)) * R) :=
      Real.log_nonneg (by nlinarith [hWnn, hR1])
    rw [hRexp]
    have hNexp_pos : 0 < (N : ℝ) ^ ((-κ) / 8) := Real.rpow_pos_of_pos hNr _
    calc (#(W N).divisors : ℝ) ^ 2 * (N : ℝ) ^ ((-κ) / 8) * Real.log (2 * ((W N : ℝ)) * R)
        ≤ LN ^ 4 * (N : ℝ) ^ ((-κ) / 8) * (K * LN) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hcard2LN hNexp_pos.le) hlog2WR hlog2WRnn
            (by positivity)
      _ = K * (LN ^ 5 * (N : ℝ) ^ ((-κ) / 8)) := by ring
      _ ≤ K * (Real.log 2 / K) := mul_le_mul_of_nonneg_left hcomp hKpos.le
      _ = Real.log 2 := by field_simp
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp hall
  exact ⟨(a : ℝ), fun N hN ↦ ha N (by exact_mod_cast hN)⟩

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- `1 / τ(V) ≤ (1 / log 2) * (φ(V) / V) * log D` for `1 ≤ V` and `2 ≤ D`, since `φ(V) / V`
dominates `1 / τ(V)` and `log D` dominates `log 2`. Both residual terms of `sharp_partial_sum`
are bounded by `1 / τ(V)`, and this is the step that turns that into the shape their callers
need. -/
private theorem one_div_card_divisors_le_totient_ratio_mul_log (V : ℕ) (hV : 1 ≤ V)
    {D : ℝ} (hD : 2 ≤ D) :
    1 / (#V.divisors : ℝ) ≤
      (1 / Real.log 2) * ((V.totient : ℝ) / (V : ℝ)) * Real.log D := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hVr1 : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  have hVr0 : (0 : ℝ) < (V : ℝ) := by linarith
  set τ : ℝ := (#V.divisors : ℝ) with hτdef
  have hτ1 : (1 : ℝ) ≤ τ := by
    rw [hτdef]
    have : 0 < #V.divisors :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega : V ≠ 0)⟩
    exact_mod_cast this
  have hτ0 : (0 : ℝ) < τ := one_pos.trans_le hτ1
  have hlogD_ge : Real.log 2 ≤ Real.log D := Real.log_le_log (by norm_num) hD
  set ratio : ℝ := ((V.totient : ℝ) / (V : ℝ)) with hratiodef
  have hratio_ge : 1 / τ ≤ ratio := by
    have htot : ((V : ℝ)) / τ ≤ (V.totient : ℝ) := by
      rw [hτdef]; exact Nat.div_card_le_totient V hV
    rw [hratiodef, div_le_div_iff₀ hτ0 hVr0]
    rw [div_le_iff₀ hτ0] at htot
    nlinarith [htot]
  have hmono : (1 / Real.log 2) * (1 / τ) * Real.log 2 ≤ (1 / Real.log 2) * ratio * Real.log D :=
    mul_le_mul (mul_le_mul_of_nonneg_left hratio_ge (by positivity)) hlogD_ge hlog2_pos.le
      (by positivity)
  have heq : (1 / Real.log 2) * (1 / τ) * Real.log 2 = 1 / τ := by
    have h1 : Real.log 2 ≠ 0 := hlog2_pos.ne'
    have h2 : τ ≠ 0 := hτ0.ne'
    field_simp
  exact heq.symm.trans_le hmono

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The `z ^ (-1/8)` residual of `sharp_partial_sum`, taken at `z = R` and `V = W N`, is at most
`c * (φ(W N) / W N) * log (D₀ N)` for all large `N`. -/
theorem residual_boundary_le_const (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) →
      ∀ (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
        (#(maynardSieveDatum N hN hD).V.divisors : ℝ) * (R) ^ ((-1 : ℝ) / 8) *
            Real.log (2 * ((maynardSieveDatum N hN hD).V : ℝ) * R) ≤
          c * (((W N).totient : ℝ) / (W N : ℝ)) *
              Real.log (PrimeGaps.D₀ (N : ℝ)) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2, by positivity, ?_⟩
  obtain ⟨x₀G, hGrow⟩ := tau_sq_rpow_log_le_log2 δ θ hδ
  refine ⟨x₀G, fun N hN₀ hN hD ↦ ?_⟩
  rw [maynardSieveDatum_V N hN hD]
  set W₀ : ℕ := W N with hWdef
  set R₀ : ℝ := R with hRdef
  set D₀ : ℝ := PrimeGaps.D₀ (N : ℝ) with hD₀def
  set τ : ℝ := (#W₀.divisors : ℝ) with hτdef
  have hW1 : 1 ≤ W₀ := hWdef ▸ PrimeGaps.W_pos
  have hτ1 : (1 : ℝ) ≤ τ := by
    rw [hτdef]
    have : 0 < #W₀.divisors :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega : W₀ ≠ 0)⟩
    exact_mod_cast this
  have hτ0 : (0 : ℝ) < τ := one_pos.trans_le hτ1
  have hGrowN : τ ^ 2 * R₀ ^ ((-1 : ℝ) / 8) * Real.log (2 * (W₀ : ℝ) * R₀) ≤ Real.log 2 := by
    have h := hGrow N hN₀
    rwa [← hWdef, ← hRdef, ← hτdef] at h
  have hlog2_le_one : Real.log 2 ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have hStepC : τ * R₀ ^ ((-1 : ℝ) / 8) * Real.log (2 * (W₀ : ℝ) * R₀) ≤ 1 / τ := by
    rw [le_div_iff₀ hτ0]
    nlinarith [hGrowN, hlog2_le_one]
  exact le_trans hStepC
    (one_div_card_divisors_le_totient_ratio_mul_log W₀ hW1 (by rw [hD₀def] at hD ⊢; exact hD))

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The `1 / log z` residual of `sharp_partial_sum`, taken at `z = R` and `V = W N`, is at most
`c * (φ(W N) / W N) * log (D₀ N)` for all large `N`. -/
theorem residual_integral_le_const (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) →
      ∀ (hN : 0 < N) (hD : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
        (#(maynardSieveDatum N hN hD).V.divisors : ℝ) *
            Real.log (2 * ((maynardSieveDatum N hN hD).V : ℝ)) /
            Real.log (R) ≤
          c * (((W N).totient : ℝ) / (W N : ℝ)) *
              Real.log (PrimeGaps.D₀ (N : ℝ)) := by
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨1 / Real.log 2, by positivity, ?_⟩
  obtain ⟨x₀W, hTau⟩ := tau_sq_log_le_logR δ θ hδ
  obtain ⟨a2, ha2⟩ := Filter.eventually_atTop.mp
    (PrimeGaps.R_eventually_ge θ δ hδ.2 2)
  refine ⟨max x₀W (max (a2 : ℝ) 1), fun N hN₀ hN hD ↦ ?_⟩
  have hxW : x₀W ≤ (N : ℝ) := le_trans (le_max_left _ _) hN₀
  have hx2 : (a2 : ℝ) ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN₀
  have h2R : ∀ (M : ℕ), (a2 : ℝ) ≤ (M : ℝ) → 2 ≤ (M : ℝ) ^ (θ / 2 - δ) :=
    fun M hM ↦ ha2 M (by exact_mod_cast hM)
  rw [maynardSieveDatum_V N hN hD]
  set W₀ : ℕ := W N with hWdef
  set R₀ : ℝ := R with hRdef
  set D₀ : ℝ := PrimeGaps.D₀ (N : ℝ) with hD₀def
  set τ : ℝ := (#W₀.divisors : ℝ) with hτdef
  set Lw : ℝ := Real.log (2 * (W₀ : ℝ)) with hLwdef
  have hW1 : 1 ≤ W₀ := hWdef ▸ PrimeGaps.W_pos
  have hτ1 : (1 : ℝ) ≤ τ := by
    rw [hτdef]
    have : 0 < #W₀.divisors :=
      Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega : W₀ ≠ 0)⟩
    exact_mod_cast this
  have hτ0 : (0 : ℝ) < τ := one_pos.trans_le hτ1
  have hR2 : 2 ≤ R₀ := h2R N hx2
  have hlogR_pos : 0 < Real.log R₀ :=
    hlog2_pos.trans_le (Real.log_le_log (by norm_num) hR2)
  have hTauN : τ ^ 2 * Lw ≤ Real.log R₀ := by
    have h := hTau N hxW
    rwa [← hWdef, ← hRdef, ← hLwdef, ← hτdef] at h
  have hStepC : τ * Lw / Real.log R₀ ≤ 1 / τ := by
    rw [div_le_div_iff₀ hlogR_pos hτ0]
    nlinarith [hTauN]
  exact le_trans hStepC
    (one_div_card_divisors_le_totient_ratio_mul_log W₀ hW1 (by rw [hD₀def] at hD ⊢; exact hD))

open scoped PrimeGaps.sieveModulus in
/-- `ellV (W N) = ∑_{p ∣ W N} log p / (p - 1) ≤ c * log (D₀ N)`, by Mertens' estimate for
`∑_{p ≤ x} log p / p`. -/
theorem ellV_W_le_const_log_D0 : ∃ c : ℝ, 0 ≤ c ∧ ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) →
      ∀ (_ : 0 < N) (_ : 2 ≤ PrimeGaps.D₀ (N : ℝ)),
        ellV (W N) ≤ c * Real.log (PrimeGaps.D₀ (N : ℝ)) := by
  obtain ⟨M₁, hM₁, hMert⟩ := primeLogSumLt_bound
  refine ⟨2 + (2 * Real.log (3 / 2) + 2 * M₁) / Real.log 2, ?_, 0, ?_⟩
  · have : 0 ≤ Real.log (3 / 2) := Real.log_nonneg (by norm_num)
    positivity
  intro N _ hN hD
  set D := PrimeGaps.D₀ (N : ℝ) with hDdef
  have hlogD_ge : Real.log 2 ≤ Real.log D := Real.log_le_log (by norm_num) hD
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hPF : (W N).primeFactors = (Finset.Icc 2 ⌊D⌋₊).filter Nat.Prime := by
    rw [PrimeGaps.W_eq_primorial_D₀, primeFactors_primorial]
    ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨hpD, hp⟩
      exact ⟨⟨hp.two_le, by simpa [hDdef] using hpD⟩, hp⟩
    · rintro ⟨⟨_, hpD⟩, hp⟩
      exact ⟨by simpa [hDdef] using hpD, hp⟩
  have hPLS : ellV (W N) = ∑ p ∈ (Finset.Icc 2 ⌊D⌋₊).filter Nat.Prime, Real.log ↑p / (↑p - 1) := by
    unfold ellV
    rw [hPF]
  have hterm : ∀ p ∈ (Finset.Icc 2 ⌊D⌋₊).filter Nat.Prime,
      Real.log ↑p / (↑p - 1) ≤ 2 * (Real.log ↑p / ↑p) := by
    intro p hp
    have hp2 : 2 ≤ p := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1
    have hpp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    rw [mul_div_assoc', div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith [hlogp, hpp]
  have hstep1 : ellV (W N) ≤ 2 * ∑ p ∈ (Finset.Icc 2 ⌊D⌋₊).filter Nat.Prime, Real.log ↑p / ↑p := by
    rw [hPLS, Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  set a : ℝ := (⌊D⌋₊ : ℝ) + 1 with hadef
  have ha2 : 2 ≤ a := by
    have h2 : (2 : ℕ) ≤ ⌊D⌋₊ := by
      rw [Nat.le_floor_iff (by linarith)]
      exact_mod_cast hD
    have : (2 : ℝ) ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast h2
    rw [hadef]; linarith
  have hfa : ⌊a⌋₊ = ⌊D⌋₊ + 1 := by
    rw [hadef, Nat.floor_add_one (by positivity)]
    simp
  have hseteq : (Finset.Icc 2 ⌊D⌋₊).filter Nat.Prime =
      {p ∈ (Finset.range (⌊a⌋₊ + 1)) | Nat.Prime p ∧ (↑p : ℝ) < a} := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range, hfa]
    constructor
    · rintro ⟨⟨h2, hle⟩, hpr⟩
      refine ⟨by omega, hpr, ?_⟩
      have : (p : ℝ) ≤ (⌊D⌋₊ : ℝ) := by exact_mod_cast hle
      rw [hadef]; linarith
    · rintro ⟨_, hpr, hreal⟩
      have hple : p ≤ ⌊D⌋₊ := by
        rw [hadef] at hreal
        exact Nat.lt_succ_iff.mp (by exact_mod_cast hreal)
      exact ⟨⟨hpr.two_le, hple⟩, hpr⟩
  have hMertBound : ∑ p ∈ (Finset.Icc 2 ⌊D⌋₊).filter Nat.Prime, Real.log ↑p / ↑p ≤
      Real.log a + M₁ := by
    rw [hseteq]
    linarith [(abs_le.mp (hMert a ha2)).2]
  have hloga : Real.log a ≤ Real.log D + Real.log (3 / 2) := by
    have haD : a ≤ D * (3 / 2) := by
      have hfl : (⌊D⌋₊ : ℝ) ≤ D := Nat.floor_le (by linarith)
      rw [hadef]
      nlinarith [hD]
    calc Real.log a ≤ Real.log (D * (3 / 2)) := Real.log_le_log (by rw [hadef]; positivity) haD
      _ = Real.log D + Real.log (3 / 2) := Real.log_mul (by linarith) (by norm_num)
  have hconst : 2 * Real.log (3 / 2) + 2 * M₁ ≤
      (2 * Real.log (3 / 2) + 2 * M₁) / Real.log 2 * Real.log D := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hlog2_pos]
    have hK : 0 ≤ 2 * Real.log (3 / 2) + 2 * M₁ := by
      linarith [Real.log_nonneg (show (1 : ℝ) ≤ 3 / 2 by norm_num)]
    nlinarith [hlogD_ge, hK]
  calc ellV (W N) ≤ 2 * ∑ p ∈ (Finset.Icc 2 ⌊D⌋₊).filter Nat.Prime, Real.log ↑p / ↑p := hstep1
    _ ≤ 2 * Real.log D + (2 * Real.log (3 / 2) + 2 * M₁) := by linarith [hMertBound, hloga]
    _ ≤ 2 * Real.log D + (2 * Real.log (3 / 2) + 2 * M₁) / Real.log 2 * Real.log D := by
        linarith [hconst]
    _ = (2 + (2 * Real.log (3 / 2) + 2 * M₁) / Real.log 2) * Real.log D := by ring

open scoped PrimeGaps.sieveTruncation in
/-- `2 ≤ R` for all large `N`. -/
theorem two_le_R (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ x₀ : ℝ, ∀ (N : ℕ), x₀ ≤ (N : ℝ) → 2 ≤ R := by
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (PrimeGaps.R_eventually_ge θ δ hδ.2 2)
  exact ⟨(a : ℝ), fun N hN ↦ ha N (by exact_mod_cast hN)⟩

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- The `rᵢ` -coordinate `g` -Mertens sum. There is a constant `C > 0` and a threshold `N₀` such
that for all `N ≥ N₀` (with `0 < N` and `2 ≤ D₀` ) and every `ContDiff ℝ 1` test function `G`,
the weighted sum `∑_{r < R, gcd(r,W)=1} μ(r)²/g(r) · G(log r / log R)` lies within
`C·(φ(W)/W)·((log R / D₀)·|∫₀¹ G| + (log D₀)·Gmax G)` of its main term
`(φ(W)/W)·(log R)·∫₀¹ G`, at the paper truncation and modulus determined by `N, δ, θ`. -/
@[pg_tag "bg246" "lem_S2m_g_coord"]
theorem lem_S2m_g_coord (δ θ : ℝ) (hδ : δ ∈ Set.Ioo (0 : ℝ) (θ / 2)) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N →
      ∀ (_ : 0 < N) (_ : 2 ≤ PrimeGaps.D₀ (N : ℝ)) (G : ℝ → ℝ), ContDiff ℝ 1 G →
        |(∑ r ∈ (Finset.range ⌈R⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R ∧ Nat.Coprime r (W N)),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log (R))) -
          ((W N).totient : ℝ) / (W N : ℝ) * Real.log (R) * (∫ x in (0 : ℝ)..1, G x)| ≤
        C * (((W N).totient : ℝ) / (W N : ℝ)) * (Real.log (R) / PrimeGaps.D₀ (N : ℝ) *
                  |∫ x in (0 : ℝ)..1, G x| + Real.log (PrimeGaps.D₀ (N : ℝ)) * Gmax G) := by
  obtain ⟨B₁, B₂, B₃, hB₁, hB₂, hB₃, hSharp⟩ := sharp_partial_sum
  obtain ⟨Cs, hCs, xs, hSing⟩ := singularSeries_maynard_asymptotic
  obtain ⟨cP, hcP, xP, hPrime⟩ := ellV_W_le_const_log_D0
  obtain ⟨cB, hcB, xB, hRbdry⟩ := residual_boundary_le_const δ θ hδ
  obtain ⟨cI, hcI, xI, hRint⟩ := residual_integral_le_const δ θ hδ
  obtain ⟨x2, h2R⟩ := two_le_R δ θ hδ
  set B₁' : ℝ := B₁ (1 / 2) 2 with hB₁'def
  set B₂' : ℝ := B₂ (1 / 2) 2 with hB₂'def
  set B₃' : ℝ := B₃ (1 / 2) 2 with hB₃'def
  have hB₁'nn : 0 ≤ B₁' := hB₁ (1 / 2) 2
  have hB₂'nn : 0 ≤ B₂' := hB₂ (1 / 2) 2
  have hB₃'nn : 0 ≤ B₃' := hB₃ (1 / 2) 2
  set K₁ : ℝ := B₁' * (1 + Cs / 2) * (1 / Real.log 2 + cP) with hK₁def
  set C : ℝ := max Cs (K₁ + B₂' * cB + B₃' * cI) with hCdef
  refine ⟨C, ?_, max xs (max xP (max xB (max xI (max x2 1)))), ?_⟩
  · exact lt_of_lt_of_le hCs (le_max_left _ _)
  intro N hN₀ hN hD G hG
  have hxs : xs ≤ (N : ℝ) := le_trans (le_max_left _ _) hN₀
  have hxP : xP ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN₀
  have hxB : xB ≤ (N : ℝ) :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hN₀
  have hxI : xI ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))) hN₀
  have hx2 : x2 ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _)
      (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_max_right _ _))))) hN₀
  set S : SieveDatum := maynardSieveDatum N hN hD with hSdef
  set R₀ : ℝ := R with hRdef
  set W₀ : ℕ := W N with hWdef
  set singular : ℝ := PrimeGaps.singularSeries S.γ with hsingulardef
  set ratio : ℝ := ((W₀).totient : ℝ) / (W₀ : ℝ) with hratiodef
  set I : ℝ := ∫ x in (0 : ℝ)..1, G x with hIdef
  set Gsup : ℝ := Gmax G with hGsupdef
  set D₀ : ℝ := PrimeGaps.D₀ (N : ℝ) with hD₀def
  have hR2 : 2 ≤ R₀ := h2R N hx2
  have hlogR_nonneg : 0 ≤ Real.log R₀ := Real.log_nonneg (by linarith)
  have hlogD₀_ge : Real.log 2 ≤ Real.log D₀ :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hD)
  have hlog2_pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogD₀_pos : 0 < Real.log D₀ := hlog2_pos.trans_le hlogD₀_ge
  have hlogD₀_nonneg : 0 ≤ Real.log D₀ := hlogD₀_pos.le
  have hD₀_pos : 0 < D₀ := by linarith [(hD : (2 : ℝ) ≤ D₀)]
  have hGsup_nonneg : 0 ≤ Gsup := by
    rw [hGsupdef]; unfold Gmax; exact Real.iSup_nonneg fun t ↦ by positivity
  have hratio_nonneg : 0 ≤ ratio := by
    rw [hratiodef]; positivity
  have hsingular_pos : 0 < singular := PrimeGaps.singularSeries_pos S
  have hI_nonneg : 0 ≤ |I| := abs_nonneg _
  have hV_eq : S.V = W₀ := by rw [hSdef, hWdef]; exact maynardSieveDatum_V N hN hD
  have hA₁ : S.A₁ = 1 / 2 := maynardSieveDatum_A₁ N hN hD
  have hA₃ : S.A₃ = 2 := maynardSieveDatum_A₃ N hN hD
  have hSharp' := hSharp S G hG R₀ hR2
  rw [sum_h_eq_muSq_g N hN hD G R₀, hA₁, hA₃, hV_eq] at hSharp'
  have hSing' := hSing N hxs hN hD
  have hPrime' := hPrime N hxP hN hD
  have hRbdry' := hRbdry N hxB hN hD
  have hRint' := hRint N hxI hN hD
  have hSing'' : |singular - ratio| ≤ Cs * ratio * (1 / D₀) := by
    rwa [hsingulardef, hratiodef, hWdef, hD₀def, hSdef]
  have hbudget1 :
      |singular * Real.log R₀ * I - ratio * Real.log R₀ * I| ≤
        Cs * ratio * (Real.log R₀ / D₀ * |I|) := by
    have hfac : singular * Real.log R₀ * I - ratio * Real.log R₀ * I =
        (singular - ratio) * (Real.log R₀ * I) := by ring
    rw [hfac, abs_mul, abs_mul, abs_of_nonneg hlogR_nonneg]
    have hrhs : Cs * ratio * (Real.log R₀ / D₀ * |I|) =
        (Cs * ratio * (1 / D₀)) * (Real.log R₀ * |I|) := by ring
    rw [hrhs]
    exact mul_le_mul_of_nonneg_right hSing'' (mul_nonneg hlogR_nonneg (abs_nonneg I))
  have hterm1 : B₁' * singular * (1 + ellV W₀) * Gsup ≤ K₁ * (ratio * Real.log D₀ * Gsup) := by
    have hSingle : singular - ratio ≤ Cs * ratio * (1 / D₀) := (le_abs_self _).trans hSing''
    have h1 : singular ≤ ratio * (1 + Cs / 2) := by
      have hCr : Cs * ratio * (1 / D₀) ≤ Cs * ratio * (1 / 2) :=
        mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le (by norm_num) hD) (by positivity)
      nlinarith [hSingle, hCr]
    have hPrime'' : ellV W₀ ≤ cP * Real.log D₀ := by
      rw [hWdef, hD₀def]; exact hPrime'
    have h2 : 1 + ellV W₀ ≤ Real.log D₀ * (1 / Real.log 2 + cP) := by
      have hone : (1 : ℝ) ≤ Real.log D₀ / Real.log 2 := (one_le_div hlog2_pos).mpr hlogD₀_ge
      have heq : Real.log D₀ * (1 / Real.log 2 + cP) =
          Real.log D₀ / Real.log 2 + cP * Real.log D₀ := by ring
      rw [heq]
      linarith [hPrime'', hone]
    have hcoef1 : 0 ≤ B₁' * singular * Gsup := by positivity
    have hcoefB : 0 ≤ B₁' * (Real.log D₀ * (1 / Real.log 2 + cP)) * Gsup := by positivity
    calc B₁' * singular * (1 + ellV W₀) * Gsup
        = (B₁' * singular * Gsup) * (1 + ellV W₀) := by ring
      _ ≤ (B₁' * singular * Gsup) * (Real.log D₀ * (1 / Real.log 2 + cP)) :=
          mul_le_mul_of_nonneg_left h2 hcoef1
      _ = (B₁' * (Real.log D₀ * (1 / Real.log 2 + cP)) * Gsup) * singular := by ring
      _ ≤ (B₁' * (Real.log D₀ * (1 / Real.log 2 + cP)) * Gsup) * (ratio * (1 + Cs / 2)) :=
          mul_le_mul_of_nonneg_left h1 hcoefB
      _ = K₁ * (ratio * Real.log D₀ * Gsup) := by rw [hK₁def]; ring
  have hterm2 : B₂' * (#W₀.divisors : ℝ) * R₀ ^ ((-1 : ℝ) / 8) *
      Real.log (2 * (W₀ : ℝ) * R₀) * Gsup ≤
      (B₂' * cB) * (ratio * Real.log D₀ * Gsup) := by
    have hRbdry'' : (#W₀.divisors : ℝ) * R₀ ^ ((-1 : ℝ) / 8) * Real.log (2 * (W₀ : ℝ) * R₀) ≤
        cB * ratio * Real.log D₀ := by
      rwa [← hSdef, hV_eq, ← hRdef, ← hWdef, ← hratiodef, ← hD₀def] at hRbdry'
    calc B₂' * (#W₀.divisors : ℝ) * R₀ ^ ((-1 : ℝ) / 8) * Real.log (2 * (W₀ : ℝ) * R₀) * Gsup
        = B₂' * ((#W₀.divisors : ℝ) * R₀ ^ ((-1 : ℝ) / 8) *
          Real.log (2 * (W₀ : ℝ) * R₀)) * Gsup := by ring
      _ ≤ B₂' * (cB * ratio * Real.log D₀) * Gsup :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRbdry'' hB₂'nn) hGsup_nonneg
      _ = (B₂' * cB) * (ratio * Real.log D₀ * Gsup) := by ring
  have hterm3 : B₃' * (#W₀.divisors : ℝ) * Real.log (2 * (W₀ : ℝ)) / Real.log R₀ * Gsup ≤
      (B₃' * cI) * (ratio * Real.log D₀ * Gsup) := by
    have hRint'' : (#W₀.divisors : ℝ) * Real.log (2 * (W₀ : ℝ)) / Real.log R₀ ≤
          cI * ratio * Real.log D₀ := by
      rwa [← hSdef, hV_eq, ← hRdef, ← hWdef, ← hratiodef, ← hD₀def] at hRint'
    calc B₃' * (#W₀.divisors : ℝ) * Real.log (2 * (W₀ : ℝ)) / Real.log R₀ * Gsup
        = B₃' * ((#W₀.divisors : ℝ) * Real.log (2 * (W₀ : ℝ)) /
          Real.log R₀) * Gsup := by ring
      _ ≤ B₃' * (cI * ratio * Real.log D₀) * Gsup :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRint'' hB₃'nn) hGsup_nonneg
      _ = (B₃' * cI) * (ratio * Real.log D₀ * Gsup) := by ring
  have htri :
      |(∑ r ∈ (Finset.range ⌈R₀⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R₀ ∧ Nat.Coprime r W₀),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log R₀)) -
          ratio * Real.log R₀ * I| ≤ |(∑ r ∈ (Finset.range ⌈R₀⌉₊).filter
              (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R₀ ∧ Nat.Coprime r W₀),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log R₀)) -
            singular * Real.log R₀ * I| +
          |singular * Real.log R₀ * I - ratio * Real.log R₀ * I| :=
    abs_sub_le _ (singular * Real.log R₀ * I) _
  calc |(∑ r ∈ (Finset.range ⌈R₀⌉₊).filter (fun r : ℕ ↦ 0 < r ∧ (r : ℝ) < R₀ ∧ Nat.Coprime r W₀),
            (μ r : ℝ) ^ 2 / (g r : ℝ) * G (Real.log r / Real.log R₀)) -
          ratio * Real.log R₀ * I| ≤
        (B₁' * singular * (1 + ellV W₀) * Gsup + B₂' * (#W₀.divisors : ℝ) * R₀ ^ ((-1 : ℝ) /
          8) * Real.log (2 * (W₀ : ℝ) * R₀) * Gsup +
          B₃' * (#W₀.divisors : ℝ) * Real.log (2 * (W₀ : ℝ)) / Real.log R₀ * Gsup) +
          Cs * ratio * (Real.log R₀ / D₀ * |I|) :=
        htri.trans (add_le_add hSharp' hbudget1)
    _ ≤ (K₁ * (ratio * Real.log D₀ * Gsup) + (B₂' * cB) * (ratio * Real.log D₀ * Gsup) +
          (B₃' * cI) * (ratio * Real.log D₀ * Gsup)) +
          Cs * ratio * (Real.log R₀ / D₀ * |I|) :=
        add_le_add (add_le_add (add_le_add hterm1 hterm2) hterm3) le_rfl
    _ = (K₁ + B₂' * cB + B₃' * cI) * (ratio * Real.log D₀ * Gsup) +
          Cs * (ratio * (Real.log R₀ / D₀ * |I|)) := by ring
    _ ≤ C * (ratio * Real.log D₀ * Gsup) +
        C * (ratio * (Real.log R₀ / D₀ * |I|)) := by
        have hnn1 : 0 ≤ ratio * Real.log D₀ * Gsup :=
          mul_nonneg (mul_nonneg hratio_nonneg hlogD₀_nonneg) hGsup_nonneg
        have hlogRD : 0 ≤ Real.log R₀ / D₀ := div_nonneg hlogR_nonneg hD₀_pos.le
        have hnn2 : 0 ≤ ratio * (Real.log R₀ / D₀ * |I|) :=
          mul_nonneg hratio_nonneg (mul_nonneg hlogRD hI_nonneg)
        exact add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) hnn1)
          (mul_le_mul_of_nonneg_right (le_max_left _ _) hnn2)
    _ = C * ratio * (Real.log R₀ / D₀ * |I| + Real.log D₀ * Gsup) := by ring

end PrimeGaps
