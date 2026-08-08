/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.Mertens.CoprimeDensity.PartialBounds

/-!
# Dyadic tail bounds

The dyadic block decomposition and the tail bounds for `gKernel`.

## Main results

* `gKernel_logtail_bound`
-/

@[expose] public section

open PrimeGaps.MertensShared Finset ArithmeticFunction

namespace PrimeGaps

/-- On a block `[a, b)` the unweighted sum is controlled by the weighted one:
`∑_{a ≤ d < b} |g d| ≤ (1/a) · ∑_{d ≤ b} |g d| · d`. -/
lemma dyTail_block_bound (g : ℕ → ℝ) (a b : ℕ) (ha : 1 ≤ a) :
    (∑ d ∈ Finset.Ico a b, |g d|) ≤ (1 / (a : ℝ)) * ∑ d ∈ Finset.Icc 1 b, |g d| * (d : ℝ) := by
  have hapos : (0 : ℝ) < (a : ℝ) := by exact_mod_cast ha
  rw [Finset.mul_sum]
  refine (Finset.sum_le_sum ?_).trans
    (Finset.sum_le_sum_of_subset_of_nonneg ?_ fun d _ _ ↦ by positivity)
  · intro d hd
    rw [Finset.mem_Ico] at hd
    have h1 : (1 : ℝ) ≤ (d : ℝ) / (a : ℝ) := (one_le_div hapos).mpr (by exact_mod_cast hd.1)
    calc |g d| = |g d| * 1 := (mul_one _).symm
      _ ≤ |g d| * ((d : ℝ) / (a : ℝ)) := by gcongr
      _ = (1 / (a : ℝ)) * (|g d| * (d : ℝ)) := by ring
  · intro d hd
    simp only [Finset.mem_Ico] at hd
    simp only [Finset.mem_Icc]
    omega

/-- Splits `[y₀, 2^J·y₀)` into the `J` dyadic blocks `[2^j·y₀, 2^(j+1)·y₀)`, for an arbitrary
summand.  Induction on `J`, peeling the top block off with `Finset.sum_Ico_consecutive`. -/
private lemma dyTail_dyadic_decomp_general (f : ℕ → ℝ) (y0 : ℕ) (J : ℕ) :
    (∑ d ∈ Finset.Ico y0 (2 ^ J * y0), f d) =
      ∑ j ∈ Finset.range J, ∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), f d := by
  induction J with
  | zero => simp
  | succ J ih =>
    rw [Finset.sum_range_succ, ← ih]
    exact (Finset.sum_Ico_consecutive f (Nat.le_mul_of_pos_left y0 (Nat.two_pow_pos J))
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right two_pos J.le_succ))).symm

/-- Splits `[y₀, 2^J·y₀)` into the `J` dyadic blocks `[2^j·y₀, 2^(j+1)·y₀)`. -/
lemma dyTail_dyadic_decomp (g : ℕ → ℝ) (y0 : ℕ) (J : ℕ) :
    (∑ d ∈ Finset.Ico y0 (2 ^ J * y0), |g d|) =
      ∑ j ∈ Finset.range J, ∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), |g d| :=
  dyTail_dyadic_decomp_general (fun d ↦ |g d|) y0 J

/-- For `Y ≥ 1` the ceiling of `Y` is positive, at least `Y`, and at most `2 * Y`. -/
lemma dyTail_ceil_bounds {Y : ℝ} (hY : 1 ≤ Y) :
    1 ≤ ⌈Y⌉₊ ∧ Y ≤ (⌈Y⌉₊ : ℝ) ∧ ((⌈Y⌉₊ : ℝ)) ≤ 2 * Y := by
  have hYpos : (0 : ℝ) < Y := by linarith
  refine ⟨Nat.one_le_ceil_iff.mpr hYpos, Nat.le_ceil Y, ?_⟩
  linarith [Nat.ceil_lt_add_one hYpos.le]

/-- The elements of `s` that are at least `Y` all lie in the dyadic window `[y₀, 2^(N+1)·y₀)`,
where `y₀ = ⌈Y⌉₊` and `N` bounds `s`.  The lower bound is `Nat.ceil_le`; the upper bound holds
because `N < 2^(N+1) ≤ 2^(N+1)·y₀`. -/
private lemma dyTail_filter_subset_Ico (s : Finset ℕ) (Y : ℝ) (y0 N : ℕ) (hy0 : y0 = ⌈Y⌉₊)
    (hy0pos : 1 ≤ y0) (hN : N = s.sup id) :
    s.filter (fun (i : ℕ) ↦ Y ≤ (i : ℝ)) ⊆ Finset.Ico y0 (2 ^ (N + 1) * y0) := by
  intro d hd
  rw [Finset.mem_filter] at hd
  rw [Finset.mem_Ico]
  refine ⟨by rw [hy0]; exact Nat.ceil_le.mpr hd.2, ?_⟩
  calc d ≤ N := by rw [hN]; exact Finset.le_sup (f := id) hd.1
    _ < 2 ^ (N + 1) := Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right two_pos N.le_succ)
    _ ≤ 2 ^ (N + 1) * y0 := Nat.le_mul_of_pos_right _ hy0pos

/-- The geometric ratio `1/√2` of the dyadic tail blocks. -/
noncomputable def dyTailRatio : ℝ := 1 / √2

/-- `dyTailRatio` is nonnegative. -/
lemma dyTailRatio_nn : 0 ≤ dyTailRatio := by unfold dyTailRatio; positivity

/-- A quadratic-times-geometric series is summable: `∑_j P(j)·rr2^j` for `P` polynomial. -/
lemma dyTail_poly_geom_summable (a b c : ℝ) :
    Summable (fun j : ℕ ↦ (a * (j : ℝ) ^ 2 + b * (j : ℝ) + c) * dyTailRatio ^ j) := by
  have hlt : dyTailRatio < 1 := by
    unfold dyTailRatio
    rw [div_lt_one (Real.sqrt_pos.mpr (by norm_num))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hnorm : ‖dyTailRatio‖ < 1 := by
    rwa [Real.norm_eq_abs, abs_of_nonneg dyTailRatio_nn]
  have hsq : Summable (fun j : ℕ ↦ (j : ℝ) ^ 2 * dyTailRatio ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 2 hnorm
  have hlin : Summable (fun j : ℕ ↦ (j : ℝ) * dyTailRatio ^ j) := by
    simpa using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  have hconst : Summable (fun j : ℕ ↦ dyTailRatio ^ j) :=
    summable_geometric_of_lt_one dyTailRatio_nn hlt
  exact (((hsq.mul_left a).add (hlin.mul_left b)).add (hconst.mul_left c)).congr fun j ↦ by ring

/-- `√(2^(j+2)) / 2^j = 2 · (1/√2)^j`. -/
lemma dyTail_sqrt_pow_identity (j : ℕ) :
    √((2 : ℝ) ^ (j + 2)) / (2 : ℝ) ^ j = 2 * dyTailRatio ^ j := by
  have h2j : (√2) ^ j * (√2) ^ j = (2 : ℝ) ^ j := by
    rw [← pow_add, ← two_mul, pow_mul, Real.sq_sqrt (by norm_num)]
  rw [show √((2 : ℝ) ^ (j + 2)) = 2 * (√2) ^ j from by
    rw [show (2 : ℝ) ^ (j + 2) = (2 * (√2) ^ j) ^ 2 from by
      rw [mul_pow, pow_two ((√2) ^ j), h2j]; ring]
    exact Real.sqrt_sq (by positivity)]
  unfold dyTailRatio
  rw [div_pow, one_pow]
  field_simp
  linarith [h2j]

/-- The `j`-th dyadic block above `Y` contributes at most
`C_A · 2 · (j + 3) · (1/√2)^j · log (2Y)/√Y`, given the weighted bound `hA`. -/
lemma dyTail_full_block_bound (g : ℕ → ℝ) (CA : ℝ) (hCA : 0 < CA)
    (hA : ∀ X : ℕ, (∑ d ∈ Finset.Icc 1 X, |g d| * (d : ℝ)) ≤ CA * √X * Real.log (2 * X))
    (Y : ℝ) (hY : 1 ≤ Y) (y0 : ℕ) (hy0lo : Y ≤ (y0 : ℝ)) (hy0hi : (y0 : ℝ) ≤ 2 * Y)
    (hy0pos : 1 ≤ y0) (j : ℕ) :
    (∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), |g d|) ≤
      CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log (2 * Y) / √Y) := by
  set a := 2 ^ j * y0 with ha_def
  set b := 2 ^ (j + 1) * y0 with hb_def
  have hapos : 1 ≤ a := Nat.one_le_two_pow.trans (Nat.le_mul_of_pos_right _ hy0pos)
  have hbge1 : 1 ≤ b := Nat.one_le_two_pow.trans (Nat.le_mul_of_pos_right _ hy0pos)
  have hb1 : (1 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hbge1
  have hYpos : (0 : ℝ) < Y := by linarith
  have hY_ne : Y ≠ 0 := hYpos.ne'
  have hac : (a : ℝ) = (2 : ℝ) ^ j * (y0 : ℝ) := by rw [ha_def]; push_cast; ring
  have hbc : (b : ℝ) = (2 : ℝ) ^ (j + 1) * (y0 : ℝ) := by rw [hb_def]; push_cast; ring
  have ha_ge : (2 : ℝ) ^ j * Y ≤ (a : ℝ) := by rw [hac]; gcongr
  have hb_le : (b : ℝ) ≤ (2 : ℝ) ^ (j + 2) * Y := by
    rw [hbc, show (2 : ℝ) ^ (j + 2) * Y = (2 : ℝ) ^ (j + 1) * (2 * Y) from by ring]
    gcongr
  have hsqrtb : √(b : ℝ) ≤ √((2 : ℝ) ^ (j + 2)) * √Y := by
    rw [← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt hb_le
  have hlog2b_nn : (0 : ℝ) ≤ Real.log (2 * (b : ℝ)) := Real.log_nonneg (by linarith)
  have hlog2b : Real.log (2 * (b : ℝ)) ≤ ((j : ℝ) + 3) * Real.log (2 * Y) := by
    have hlogYnn : (0 : ℝ) ≤ Real.log Y := Real.log_nonneg hY
    calc Real.log (2 * (b : ℝ)) ≤ Real.log ((2 : ℝ) ^ (j + 3) * Y) :=
          Real.log_le_log (by linarith) (by
            rw [show (2 : ℝ) ^ (j + 3) * Y = 2 * ((2 : ℝ) ^ (j + 2) * Y) from by ring]; linarith)
      _ = ((j : ℝ) + 3) * Real.log 2 + Real.log Y := by
            rw [Real.log_mul (by positivity) hY_ne, Real.log_pow]; push_cast; ring
      _ ≤ ((j : ℝ) + 3) * Real.log (2 * Y) := by
            rw [Real.log_mul two_ne_zero hY_ne]
            linarith only [mul_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ (j : ℝ)) hlogYnn, hlogYnn]
  refine ((dyTail_block_bound g a b hapos).trans
    (mul_le_mul_of_nonneg_left (hA b) (by positivity))).trans ?_
  calc (1 / (a : ℝ)) * (CA * √(b : ℝ) * Real.log (2 * (b : ℝ)))
      ≤ (1 / ((2 : ℝ) ^ j * Y)) * (CA * (√((2 : ℝ) ^ (j + 2)) * √Y) *
          (((j : ℝ) + 3) * Real.log (2 * Y))) := by gcongr
    _ = CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log (2 * Y) / √Y) := by
        rw [show (1 / ((2 : ℝ) ^ j * Y)) * (CA * (√((2 : ℝ) ^ (j + 2)) * √Y) *
                (((j : ℝ) + 3) * Real.log (2 * Y))) =
              CA * (√((2 : ℝ) ^ (j + 2)) / (2 : ℝ) ^ j) * ((j : ℝ) + 3) *
                (√Y / Y) * Real.log (2 * Y) from by field_simp,
          dyTail_sqrt_pow_identity j, Real.sqrt_div_self']
        ring

/-- Summing the dyadic blocks: `∑_{d ≥ Y} |g d| ≤ C · log (2Y)/√Y`, where the geometric series
`∑_j (j + 3)·(1/√2)^j` supplies the constant. -/
lemma dyTail_tail_wrapper (g : ℕ → ℝ) (CA : ℝ) (hCA : 0 < CA)
    (hA : ∀ X : ℕ, (∑ d ∈ Finset.Icc 1 X, |g d| * (d : ℝ)) ≤ CA * √X * Real.log (2 * X))
    (Y : ℝ) (hY : 1 ≤ Y) :
    (∑' d : ℕ, if (Y ≤ (d : ℝ)) then |g d| else 0) ≤
      (CA * 2 * (∑' j : ℕ, ((j : ℝ) + 3) * dyTailRatio ^ j)) * Real.log (2 * Y) / √Y := by
  set y0 := ⌈Y⌉₊ with hy0def
  have hYpos : (0 : ℝ) < Y := by linarith
  obtain ⟨hy0pos, hy0lo, hy0hi⟩ := dyTail_ceil_bounds hY
  have hgeoS : Summable (fun j : ℕ ↦ ((j : ℝ) + 3) * dyTailRatio ^ j) :=
    (dyTail_poly_geom_summable 0 1 3).congr fun j ↦ by ring
  have hgeoNN : (0 : ℝ) ≤ ∑' j : ℕ, ((j : ℝ) + 3) * dyTailRatio ^ j :=
    tsum_nonneg fun j ↦ mul_nonneg (by positivity) (pow_nonneg dyTailRatio_nn j)
  have hlogY : (0 : ℝ) ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  apply tsum_le_of_sum_le'
  · positivity
  · intro s
    classical
    rw [← Finset.sum_filter]
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (dyTail_filter_subset_Ico s Y y0 (s.sup id) hy0def hy0pos rfl)
      fun d _ _ ↦ abs_nonneg _).trans ?_
    rw [dyTail_dyadic_decomp g y0 (s.sup id + 1)]
    calc (∑ j ∈ Finset.range (s.sup id + 1),
          ∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), |g d|) ≤
        ∑ j ∈ Finset.range (s.sup id + 1),
            CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log (2 * Y) / √Y) :=
          Finset.sum_le_sum fun j _ ↦
            dyTail_full_block_bound g CA hCA hA Y hY y0 hy0lo hy0hi hy0pos j
      _ = (CA * 2 * (Real.log (2 * Y) / √Y)) *
            ∑ j ∈ Finset.range (s.sup id + 1), ((j : ℝ) + 3) * dyTailRatio ^ j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ ≤ (CA * 2 * (Real.log (2 * Y) / √Y)) *
            ∑' j : ℕ, ((j : ℝ) + 3) * dyTailRatio ^ j := by
          gcongr
          exact hgeoS.sum_le_tsum _ fun i _ ↦
            mul_nonneg (by positivity) (pow_nonneg dyTailRatio_nn i)
      _ = (CA * 2 * (∑' j : ℕ, ((j : ℝ) + 3) * dyTailRatio ^ j)) * Real.log (2 * Y) / √Y :=
          by ring

/-- **LEM-B (tail bound, one log).**  The tail of `|g|` decays like `log(2Y)/√Y`: there is an
absolute constant `C_B` with `∑_{d ≥ Y} |g(d)| ≤ C_B·log(2Y)/√Y` for every real `Y ≥ 1`.
Derived dyadically from `gKernel_partial_weighted_bound`: on the block `d ∈ [2^j Y, 2^{j+1} Y)`,
`∑ |g(d)| ≤ (1/(2^j Y))·∑_{d < 2^{j+1} Y} |g(d)|·d ≤ (C_A/(2^j Y))·√(2^{j+1} Y)·log(2·2^{j+1}Y)`,
and `∑_j 2^{-j/2}·((j+2)log2 + log(2Y))` converges, telescoping to `C_B·log(2Y)/√Y`. -/
lemma gKernel_tail_bound : ∃ CB : ℝ, 0 < CB ∧ ∀ Y : ℝ, 1 ≤ Y →
      (∑' d : ℕ, if (Y ≤ (d : ℝ)) then |gKernel d| else 0) ≤
        CB * Real.log (2 * Y) / √Y := by
  obtain ⟨CA, hCA, hLEMA⟩ := gKernel_partial_weighted_bound
  have hgeoS : Summable (fun j : ℕ ↦ ((j : ℝ) + 3) * dyTailRatio ^ j) :=
    (dyTail_poly_geom_summable 0 1 3).congr fun j ↦ by ring
  have hgeopos : (0 : ℝ) < ∑' j : ℕ, ((j : ℝ) + 3) * dyTailRatio ^ j := by
    have h3 : ((0 : ℝ) + 3) * dyTailRatio ^ 0 ≤ ∑' j : ℕ, ((j : ℝ) + 3) * dyTailRatio ^ j := by
      simpa using hgeoS.le_tsum 0 fun i _ ↦
        mul_nonneg (by positivity) (pow_nonneg dyTailRatio_nn i)
    norm_num at h3
    linarith
  exact ⟨CA * 2 * (∑' j : ℕ, ((j : ℝ) + 3) * dyTailRatio ^ j), by positivity,
    fun Y hY ↦ dyTail_tail_wrapper gKernel CA hCA hLEMA Y hY⟩

/-- If the weighted partial sums of `g` grow at most as `√X log(2X)`, then its shifted-log
tail is at most a constant multiple of `log(2Y)/√Y`. -/
lemma dyTail_logtail_wrapper (g : ℕ → ℝ) (CA : ℝ) (hCA : 0 < CA)
    (hA : ∀ X : ℕ, (∑ d ∈ Finset.Icc 1 X, |g d| * (d : ℝ)) ≤ CA * √X * Real.log (2 * X))
    (Y : ℝ) (hY : 1 ≤ Y) :
    (∑' d : ℕ, if (Y ≤ (d : ℝ)) then |g d| * Real.log ((d : ℝ) / Y) else 0) ≤
      (CA * 2 * Real.log 2 * (∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j)) *
          Real.log (2 * Y) / √Y := by
  set y0 := ⌈Y⌉₊ with hy0def
  have hYpos : (0 : ℝ) < Y := by linarith
  obtain ⟨hy0pos, hy0lo, hy0hi⟩ := dyTail_ceil_bounds hY
  have hgeoS : Summable (fun j : ℕ ↦ ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j) :=
    (dyTail_poly_geom_summable 1 5 6).congr fun j ↦ by ring
  have hgeoNN : (0 : ℝ) ≤ ∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j :=
    tsum_nonneg fun j ↦ mul_nonneg (by positivity) (pow_nonneg dyTailRatio_nn j)
  have hlogY : (0 : ℝ) ≤ Real.log (2 * Y) := Real.log_nonneg (by linarith)
  apply tsum_le_of_sum_le'
  · positivity
  · intro s
    classical
    rw [← Finset.sum_filter]
    refine (Finset.sum_le_sum_of_subset_of_nonneg
      (dyTail_filter_subset_Ico s Y y0 (s.sup id) hy0def hy0pos rfl) fun d hd _ ↦ by
        rw [Finset.mem_Ico] at hd
        exact mul_nonneg (abs_nonneg _) (Real.log_nonneg ((one_le_div hYpos).mpr
          (hy0lo.trans (by exact_mod_cast hd.1))))).trans ?_
    rw [dyTail_dyadic_decomp_general (fun d ↦ |g d| * Real.log ((d : ℝ) / Y)) y0 (s.sup id + 1)]
    have hblockbd : ∀ j ∈ Finset.range (s.sup id + 1),
        (∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), |g d| * Real.log ((d : ℝ) / Y)) ≤
          ((j : ℝ) + 2) * Real.log 2 *
            (CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log (2 * Y) / √Y)) := by
      intro j _
      have hlogbound : ∀ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0),
          |g d| * Real.log ((d : ℝ) / Y) ≤ ((j : ℝ) + 2) * Real.log 2 * |g d| := by
        intro d hd
        rw [Finset.mem_Ico] at hd
        have hd1 : (1 : ℝ) ≤ (d : ℝ) := by
          exact_mod_cast (Nat.one_le_two_pow.trans (Nat.le_mul_of_pos_right _ hy0pos)).trans hd.1
        have hdub : (d : ℝ) < 2 ^ (j + 1) * (y0 : ℝ) := by exact_mod_cast hd.2
        have hlog_le : Real.log ((d : ℝ) / Y) ≤ ((j : ℝ) + 2) * Real.log 2 := by
          have hdY2 : (d : ℝ) / Y ≤ (2 : ℝ) ^ (j + 2) := by
            rw [div_le_iff₀ hYpos]
            calc (d : ℝ) ≤ 2 ^ (j + 1) * (y0 : ℝ) := hdub.le
              _ ≤ 2 ^ (j + 1) * (2 * Y) := by gcongr
              _ = 2 ^ (j + 2) * Y := by ring
          calc Real.log ((d : ℝ) / Y) ≤ Real.log ((2 : ℝ) ^ (j + 2)) :=
                Real.log_le_log (div_pos (by linarith) hYpos) hdY2
            _ = ((j : ℝ) + 2) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
        exact (mul_le_mul_of_nonneg_left hlog_le (abs_nonneg _)).trans_eq (mul_comm _ _)
      calc (∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), |g d| * Real.log ((d : ℝ) / Y))
          ≤ ∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), ((j : ℝ) + 2) * Real.log 2 * |g d| :=
            Finset.sum_le_sum hlogbound
        _ = ((j : ℝ) + 2) * Real.log 2 *
              (∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), |g d|) := by rw [Finset.mul_sum]
        _ ≤ ((j : ℝ) + 2) * Real.log 2 *
            (CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log (2 * Y) / √Y)) := by
            gcongr
            exact dyTail_full_block_bound g CA hCA hA Y hY y0 hy0lo hy0hi hy0pos j
    calc (∑ j ∈ Finset.range (s.sup id + 1),
            ∑ d ∈ Finset.Ico (2 ^ j * y0) (2 ^ (j + 1) * y0), |g d| * Real.log ((d : ℝ) / Y)) ≤
        ∑ j ∈ Finset.range (s.sup id + 1), ((j : ℝ) + 2) * Real.log 2 *
              (CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log (2 * Y) / √Y)) :=
          Finset.sum_le_sum hblockbd
      _ = (CA * 2 * Real.log 2 * (Real.log (2 * Y) / √Y)) *
            ∑ j ∈ Finset.range (s.sup id + 1), ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ ↦ by ring
      _ ≤ (CA * 2 * Real.log 2 * (Real.log (2 * Y) / √Y)) *
            ∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j := by
          gcongr
          exact hgeoS.sum_le_tsum _ fun i _ ↦
            mul_nonneg (by positivity) (pow_nonneg dyTailRatio_nn i)
      _ = (CA * 2 * Real.log 2 * (∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j)) *
            Real.log (2 * Y) / √Y := by ring

/-- If the weighted partial sums of `g` grow at most as `√X log(2X)`, then every finite
partial sum of `|g d| log(2d)` has a uniform bound. -/
lemma dyTail_logfull_partial (g : ℕ → ℝ) (CA : ℝ) (hCA : 0 < CA)
    (hA : ∀ X : ℕ, (∑ d ∈ Finset.Icc 1 X, |g d| * (d : ℝ)) ≤ CA * √X * Real.log (2 * X))
    (hg0 : g 0 = 0) (s : Finset ℕ) :
    (∑ d ∈ s, |g d| * Real.log (2 * (d : ℝ))) ≤ (CA * 2 * Real.log 2 *
        (∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j)) * Real.log 2 := by
  classical
  have hgeoS : Summable (fun j : ℕ ↦ ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j) :=
    (dyTail_poly_geom_summable 1 5 6).congr fun j ↦ by ring
  rw [show (∑ d ∈ s, |g d| * Real.log (2 * (d : ℝ))) =
      ∑ d ∈ {d ∈ s | 1 ≤ d}, |g d| * Real.log (2 * (d : ℝ)) from
    (Finset.sum_filter_of_ne fun d _ h ↦
      Nat.pos_of_ne_zero fun h0 ↦ h (by simp [h0, hg0])).symm]
  have hsub : {d ∈ s | 1 ≤ d} ⊆ Finset.Ico 1 (2 ^ (s.sup id + 1)) := by
    intro d hd
    rw [Finset.mem_filter] at hd
    rw [Finset.mem_Ico]
    exact ⟨hd.2, (Finset.le_sup (f := id) hd.1).trans_lt
      (Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right two_pos (Nat.le_succ _)))⟩
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun d hd _ ↦ by
    rw [Finset.mem_Ico] at hd
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd.1
    exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))).trans ?_
  rw [show (∑ d ∈ Finset.Ico 1 (2 ^ (s.sup id + 1)), |g d| * Real.log (2 * (d : ℝ))) =
      ∑ j ∈ Finset.range (s.sup id + 1),
        ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), |g d| * Real.log (2 * (d : ℝ)) from by
    simpa using dyTail_dyadic_decomp_general (fun d ↦ |g d| * Real.log (2 * (d : ℝ))) 1 _]
  have hblockbd : ∀ j ∈ Finset.range (s.sup id + 1),
      (∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), |g d| * Real.log (2 * (d : ℝ))) ≤
        ((j : ℝ) + 2) * Real.log 2 *
            (CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log 2 / √1)) := by
    intro j _
    have hlogbound : ∀ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)),
        |g d| * Real.log (2 * (d : ℝ)) ≤ ((j : ℝ) + 2) * Real.log 2 * |g d| := by
      intro d hd
      rw [Finset.mem_Ico] at hd
      have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast Nat.one_le_two_pow.trans hd.1
      have hdub : (d : ℝ) < 2 ^ (j + 1) := by exact_mod_cast hd.2
      have hlog_le : Real.log (2 * (d : ℝ)) ≤ ((j : ℝ) + 2) * Real.log 2 := by
        have h2d : 2 * (d : ℝ) ≤ (2 : ℝ) ^ (j + 2) := by
          have : (2 : ℝ) ^ (j + 2) = 2 * 2 ^ (j + 1) := by ring
          linarith
        calc Real.log (2 * (d : ℝ)) ≤ Real.log ((2 : ℝ) ^ (j + 2)) :=
              Real.log_le_log (by linarith) h2d
          _ = ((j : ℝ) + 2) * Real.log 2 := by rw [Real.log_pow]; push_cast; ring
      exact (mul_le_mul_of_nonneg_left hlog_le (abs_nonneg _)).trans_eq (mul_comm _ _)
    calc (∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), |g d| * Real.log (2 * (d : ℝ)))
        ≤ ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), ((j : ℝ) + 2) * Real.log 2 * |g d| :=
          Finset.sum_le_sum hlogbound
      _ = ((j : ℝ) + 2) * Real.log 2 * (∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), |g d|) := by
            rw [Finset.mul_sum]
      _ ≤ ((j : ℝ) + 2) * Real.log 2 *
            (CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log 2 / √1)) := by
          gcongr
          simpa using dyTail_full_block_bound g CA hCA hA 1 le_rfl 1
            (by norm_num) (by norm_num) le_rfl j
  calc (∑ j ∈ Finset.range (s.sup id + 1),
        ∑ d ∈ Finset.Ico (2 ^ j) (2 ^ (j + 1)), |g d| * Real.log (2 * (d : ℝ))) ≤
      ∑ j ∈ Finset.range (s.sup id + 1), ((j : ℝ) + 2) * Real.log 2 *
            (CA * 2 * ((j : ℝ) + 3) * dyTailRatio ^ j * (Real.log 2 / √1)) :=
        Finset.sum_le_sum hblockbd
    _ = (CA * 2 * Real.log 2 * Real.log 2) *
          ∑ j ∈ Finset.range (s.sup id + 1), ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ ↦ by rw [Real.sqrt_one]; ring
    _ ≤ (CA * 2 * Real.log 2 * Real.log 2) *
          ∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j := by
        gcongr
        exact hgeoS.sum_le_tsum _ fun i _ ↦
          mul_nonneg (by positivity) (pow_nonneg dyTailRatio_nn i)
    _ = (CA * 2 * Real.log 2 * (∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j)) *
          Real.log 2 := by ring

/-- **LEM-C (log-weighted summability and tail).**  The `log`-weighted series `∑ |g(d)|·log(2d)`
converges to an absolute constant `κ`, and its tail decays like `log(2Y)/√Y`: there is an
absolute constant `C_C` with all of: summability, `∑' d, |g(d)|·log(2d) ≤ C_C`, and
`∑_{d ≥ Y} |g(d)|·log(2d) ≤ C_C·log(2Y)/√Y` for every real `Y ≥ 1`.  The tail follows
dyadically from `gKernel_partial_weighted_bound` (the `log` factor produces the `log(2Y)`). -/
lemma gKernel_logtail_bound : ∃ CC : ℝ, 0 < CC ∧
      Summable (fun d : ℕ ↦ |gKernel d| * Real.log (2 * d)) ∧
      (∑' d : ℕ, |gKernel d| * Real.log (2 * d)) ≤ CC ∧
      (∀ Y : ℝ, 1 ≤ Y →
        (∑' d : ℕ, if (Y ≤ (d : ℝ)) then |gKernel d| * Real.log ((d : ℝ) / Y) else 0) ≤
          CC * Real.log (2 * Y) / √Y) := by
  obtain ⟨CA, hCA, hLEMA⟩ := gKernel_partial_weighted_bound
  have hg0 : gKernel 0 = 0 := by simp [gKernel]
  set S := ∑' j : ℕ, ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j with hSdef
  have hgeoS : Summable (fun j : ℕ ↦ ((j : ℝ) + 2) * ((j : ℝ) + 3) * dyTailRatio ^ j) :=
    (dyTail_poly_geom_summable 1 5 6).congr fun j ↦ by ring
  have hSpos : (0 : ℝ) < S := by
    have h6 : ((0 : ℝ) + 2) * ((0 : ℝ) + 3) * dyTailRatio ^ 0 ≤ S := by
      rw [hSdef]
      simpa using hgeoS.le_tsum 0 fun i _ ↦
        mul_nonneg (by positivity) (pow_nonneg dyTailRatio_nn i)
    norm_num at h6; linarith
  have hlog2_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set K := CA * 2 * Real.log 2 * S with hKdef
  have hKpos : (0 : ℝ) < K := by rw [hKdef]; positivity
  have hpart : ∀ t : Finset ℕ, (∑ d ∈ t, |gKernel d| * Real.log (2 * (d : ℝ))) ≤
      K * (Real.log 2 + 1) := by
    intro t
    have h := dyTail_logfull_partial gKernel CA hCA hLEMA hg0 t
    rw [← hSdef, ← hKdef] at h
    nlinarith [mul_pos hKpos hlog2_pos]
  refine ⟨K * (Real.log 2 + 1), by positivity, ?_, tsum_le_of_sum_le' (by positivity) hpart, ?_⟩
  · refine summable_of_sum_le (fun d ↦ ?_) hpart
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd; simp
    · have : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
      exact mul_nonneg (abs_nonneg _) (Real.log_nonneg (by linarith))
  · intro Y hY
    have hw := dyTail_logtail_wrapper gKernel CA hCA hLEMA Y hY
    rw [← hSdef, ← hKdef] at hw
    exact hw.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by nlinarith [mul_pos hKpos hlog2_pos])
        (Real.log_nonneg (by linarith))) (Real.sqrt_nonneg _))

end PrimeGaps
