/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.TdDecomposition.Summands

import PrimeGapsTheory.Tactic.PaperTag

/-!
# Evaluating Td

The main and tail parts of the `T` evaluation and their assembly.

## Main results

* `slem_T_d_eval`
-/

@[expose] public section

open Real

open scoped ArithmeticFunction.Moebius

open ArithmeticFunction

namespace PrimeGaps

/-- Tail-truncation for `B`: `|B M - ∑_{e ∈ Icc 1 m} BSummand M e| ≤ (log m + 1) / m` for
`m ≥ 3`. -/
theorem B_sub_partial_bound (M : ℕ) (m : ℕ) (hm : 3 ≤ m) :
    |B M - ∑ e ∈ Finset.Icc 1 m, BSummand M e| ≤ (Real.log m + 1) / m := by
  have hbound : ∀ e : ℕ, ‖BSummand M e‖ ≤ Real.log e / (e : ℝ) ^ 2 := fun e ↦ by
    rw [Real.norm_eq_abs]
    unfold BSummand
    split_ifs
    · exact abs_moebius_mul_div_sq_le e (Real.log_natCast_nonneg e)
    · simp only [abs_zero]; positivity
  have hshift :
      Summable (fun n : ℕ ↦ Real.log ((n + m + 1 : ℕ) : ℝ) / ((n + m + 1 : ℕ) : ℝ) ^ 2) := by
    refine ((summable_nat_add_iff (m + 1)).mpr Real.summable_log_div_sq).congr fun n ↦ ?_
    congr 2
  have hnorm : Summable (fun n : ℕ ↦ ‖BSummand M (n + (m + 1))‖) :=
    .of_nonneg_of_le (fun _ ↦ norm_nonneg _) (fun _ ↦ hbound _) hshift
  have hkey : B M - ∑ e ∈ Finset.Icc 1 m, BSummand M e = ∑' n : ℕ, BSummand M (n + (m + 1)) := by
    have hIcc : Finset.Icc 1 m = (Finset.range (m + 1)).erase 0 := by
      ext x; simp only [Finset.mem_Icc, Finset.mem_erase, Finset.mem_range]; omega
    have hB : B M = ∑' e : ℕ, BSummand M e := rfl
    rw [hB, hIcc, Finset.sum_erase _ (by simp [BSummand]),
      ← (summable_BSummand M).sum_add_tsum_nat_add (m + 1)]
    ring
  rw [hkey, ← Real.norm_eq_abs]
  calc ‖∑' n : ℕ, BSummand M (n + (m + 1))‖ ≤ ∑' n : ℕ, ‖BSummand M (n + (m + 1))‖ :=
        norm_tsum_le_tsum_norm hnorm
    _ ≤ ∑' n : ℕ, Real.log ((n + m + 1 : ℕ) : ℝ) / ((n + m + 1 : ℕ) : ℝ) ^ 2 :=
        Summable.tsum_le_tsum (fun _ ↦ hbound _) hnorm hshift
    _ ≤ (Real.log m + 1) / m := Real.tail_log_div_sq_le m hm

/-- The middle-error weight `1 + log log(e₀·d·W)` is bounded by
`c₀·(log(2d) + log log W)` with `c₀ = (1+log 2)/log 2 + 1`, provided `d ≥ 1` and
`log W ≥ 1` (i.e. `W ≥ e`).  Here `e₀ = Real.exp 1`. -/
theorem loglog_conversion (d W : ℕ) (hd : 1 ≤ d) (hW : rexp 1 ≤ (W : ℝ)) :
    1 + Real.log (Real.log (rexp 1 * ((d : ℝ) * W))) ≤ ((1 + Real.log 2) / Real.log 2 + 1) *
        (Real.log (2 * d) + Real.log (Real.log W)) := by
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  have hepos : (0 : ℝ) < rexp 1 := Real.exp_pos 1
  have hWpos : (0 : ℝ) < (W : ℝ) := lt_of_lt_of_le hepos hW
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlogW_ge1 : (1 : ℝ) ≤ Real.log W := by simpa using Real.log_le_log hepos hW
  set u : ℝ := 1 + Real.log d with hu
  set v : ℝ := Real.log W with hv
  have hu1 : (1 : ℝ) ≤ u := by simp only [hu]; linarith [Real.log_nonneg hdR]
  have hupos : (0 : ℝ) < u := by linarith
  have hvpos : (0 : ℝ) < v := by linarith
  have hstepA : Real.log (rexp 1 * ((d : ℝ) * W)) = u + v := by
    rw [Real.log_mul hepos.ne' (by positivity), Real.log_exp, Real.log_mul hdpos.ne' hWpos.ne']
    simp only [hu, hv]; ring
  have hstepB : Real.log (u + v) ≤ Real.log 2 + Real.log u + Real.log v :=
    calc Real.log (u + v) ≤ Real.log (2 * u * v) :=
          Real.log_le_log (by linarith) <| by
            linarith only [mul_nonneg (by linarith : (0 : ℝ) ≤ u - 1) (by linarith : (0 : ℝ) ≤ v -
              1),
              mul_le_mul hu1 hlogW_ge1 (by linarith) (by linarith)]
      _ = Real.log 2 + Real.log u + Real.log v := by
          rw [Real.log_mul (by positivity) hvpos.ne', Real.log_mul (by norm_num) hupos.ne']
  have hlogu_le : Real.log u ≤ Real.log (2 * (d : ℝ)) :=
    Real.log_le_log hupos <| by
      simp only [hu]; linarith [Real.log_le_sub_one_of_pos hdpos]
  have hXge : Real.log 2 ≤ Real.log (2 * (d : ℝ)) + Real.log v := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : (2 : ℝ) ≤ 2 * (d : ℝ))
    linarith [Real.log_nonneg hlogW_ge1]
  rw [hstepA, add_mul, one_mul]
  set c : ℝ := (1 + Real.log 2) / Real.log 2 with hc
  have hcnn : (0 : ℝ) ≤ c := by rw [hc]; exact div_nonneg (by linarith) hlog2pos.le
  have hcancel : c * Real.log 2 = 1 + Real.log 2 := by rw [hc]; field_simp
  linarith [mul_le_mul_of_nonneg_left hXge hcnn]

/-- The truncated `A`/`B` partial sums combine into a single Möbius-weighted sum:
`L·∑_{e ≤ m} ASummand M e − 2·∑_{e ≤ m} BSummand M e` equals
`∑_{e ≤ m, (e,M)=1} (μ(e)/e²)·(L − 2 log e)`. -/
private lemma sum_ASummand_mul_sub_two_mul_sum_BSummand (M m : ℕ) (L : ℝ) :
    L * (∑ e ∈ Finset.Icc 1 m, ASummand M e) - 2 * (∑ e ∈ Finset.Icc 1 m, BSummand M e) =
      ∑ e ∈ {e ∈ Finset.Icc 1 m | Nat.Coprime e M},
        (μ e : ℝ) / (e : ℝ) ^ 2 * (L - 2 * Real.log e) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_filter]
  refine Finset.sum_congr rfl fun e _ ↦ ?_
  unfold ASummand BSummand
  split_ifs with h <;> ring

/-- Replacing the constants `A M` and `B M` by their partial sums over `Finset.Icc 1 m`
changes the leading term `g·(L·A M − 2·B M)` by at most `(Lmax + 2 log m + 2)/m`, whenever
`0 ≤ g ≤ 1`, `0 ≤ L ≤ Lmax`, `1 ≤ Lmax` and `3 ≤ m`. -/
private lemma abs_partial_leading_sub_le (M m : ℕ) (hm : 3 ≤ m) {g L Lmax : ℝ}
    (hg : 0 ≤ g) (hg1 : g ≤ 1) (hL : 0 ≤ L) (hLmax : L ≤ Lmax) (h1Lmax : 1 ≤ Lmax) :
    |g * (L * (∑ e ∈ Finset.Icc 1 m, ASummand M e) -
          2 * (∑ e ∈ Finset.Icc 1 m, BSummand M e)) - g * (A M * L - 2 * B M)| ≤
      (Lmax + 2 * Real.log m + 2) / m := by
  set S1 : ℝ := ∑ e ∈ Finset.Icc 1 m, ASummand M e with hS1
  set S2 : ℝ := ∑ e ∈ Finset.Icc 1 m, BSummand M e with hS2
  have hS1A : |S1 - A M| ≤ 1 / m := by
    rw [abs_sub_comm]; exact A_sub_partial_bound M m (by omega)
  have hS2B : |S2 - B M| ≤ (Real.log m + 1) / m := by
    rw [abs_sub_comm]; exact B_sub_partial_bound M m hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hkey : g * (L * S1 - 2 * S2) - g * (A M * L - 2 * B M) =
      g * (L * (S1 - A M) - 2 * (S2 - B M)) := by ring
  rw [hkey, abs_mul, abs_of_nonneg hg]
  have hinner : |L * (S1 - A M) - 2 * (S2 - B M)| ≤
      Lmax * (1 / (m : ℝ)) + 2 * ((Real.log m + 1) / m) :=
    calc |L * (S1 - A M) - 2 * (S2 - B M)| ≤ |L * (S1 - A M)| + |2 * (S2 - B M)| := abs_sub _ _
      _ = L * |S1 - A M| + 2 * |S2 - B M| := by
            rw [abs_mul, abs_mul, abs_of_nonneg hL, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      _ ≤ Lmax * (1 / (m : ℝ)) + 2 * ((Real.log m + 1) / m) := by
            have h1 : L * |S1 - A M| ≤ Lmax * (1 / (m : ℝ)) :=
              mul_le_mul hLmax hS1A (abs_nonneg _) (by linarith only [h1Lmax])
            have h2 : 2 * |S2 - B M| ≤ 2 * ((Real.log m + 1) / m) := by linarith only [hS2B]
            linarith
  calc g * |L * (S1 - A M) - 2 * (S2 - B M)|
      ≤ 1 * (Lmax * (1 / (m : ℝ)) + 2 * ((Real.log m + 1) / m)) :=
        mul_le_mul hg1 hinner (abs_nonneg _) (by norm_num)
    _ = (Lmax + 2 * Real.log m + 2) / m := by field_simp; ring

/-- **Möbius-weighted inner sums against their leading term.**  Suppose that for every
`1 ≤ e ≤ R^{1/8}` coprime to `d · W` the harmonic sum `∑_{w ≤ R/(d e²), (w, dW) = 1} 1/w`
lies within `K` of `g · (log R − log d − 2 log e)`.  Then the `e`-truncated Möbius-weighted
sum of those harmonic sums lies within `2 · K` of
`g · (log (R/d) · ∑_{e ≤ ⌊R^{1/8}⌋} ASummand − 2 · ∑_{e ≤ ⌊R^{1/8}⌋} BSummand)`;
the factor `2` is the bound `∑_{e ≥ 1} 1/e² ≤ 2`. -/
private lemma abs_sum_moebius_inner_sub_partial_leading_le {d W : ℕ} {R g K : ℝ}
    (hRpos : 0 < R) (hd : 0 < d) (hRR8 : R ^ (1 / 8 : ℝ) ≤ √(R / d)) (hK : 0 ≤ K)
    (hterm : ∀ e ∈ {e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊ | Nat.Coprime e (d * W)},
      |(∑ w ∈ Finset.Icc 1 ⌊R / ((d : ℝ) * (e : ℝ) ^ 2)⌋₊ with Nat.Coprime w (d * W),
            1 / (w : ℝ)) - g * (Real.log R - Real.log d - 2 * Real.log e)| ≤ K) :
    |(∑ e ∈ {e ∈ Finset.Icc 1 ⌊√(R / d)⌋₊ |
            Nat.Coprime e (d * W) ∧ (e : ℝ) ≤ R ^ (1 / 8 : ℝ)},
          (μ e : ℝ) / (e : ℝ) ^ 2 *
            (∑ w ∈ Finset.Icc 1 ⌊R / ((d : ℝ) * (e : ℝ) ^ 2)⌋₊ with Nat.Coprime w (d * W),
              1 / (w : ℝ))) -
        g * (Real.log (R / d) * (∑ e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊, ASummand (d * W) e) -
          2 * (∑ e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊, BSummand (d * W) e))| ≤ 2 * K := by
  have hR8_pos : (0 : ℝ) < R ^ (1 / 8 : ℝ) := by positivity
  set m : ℕ := ⌊R ^ (1 / 8 : ℝ)⌋₊ with hm
  set E : Finset ℕ := {e ∈ Finset.Icc 1 m | Nat.Coprime e (d * W)} with hE
  have hEsub : E ⊆ Finset.Icc 1 m := Finset.filter_subset _ _
  have hsetE : {e ∈ Finset.Icc 1 ⌊√(R / d)⌋₊ |
      Nat.Coprime e (d * W) ∧ (e : ℝ) ≤ R ^ (1 / 8 : ℝ)} = E := by
    rw [hE, hm]
    exact filter_Icc_floor_and_natCast_le_eq hR8_pos.le hRR8 _
  have hlead_E : g * (Real.log (R / d) * (∑ e ∈ Finset.Icc 1 m, ASummand (d * W) e) -
        2 * (∑ e ∈ Finset.Icc 1 m, BSummand (d * W) e)) =
      ∑ e ∈ E, (μ e : ℝ) / (e : ℝ) ^ 2 *
        (g * (Real.log R - Real.log d - 2 * Real.log e)) := by
    have hlogRd : Real.log (R / d) = Real.log R - Real.log d :=
      Real.log_div (ne_of_gt hRpos) (by exact_mod_cast hd.ne')
    rw [sum_ASummand_mul_sub_two_mul_sum_BSummand (d * W) m (Real.log (R / d)), hE, Finset.mul_sum]
    exact Finset.sum_congr rfl fun e _ ↦ by rw [hlogRd]; ring
  rw [hsetE, hlead_E, ← Finset.sum_sub_distrib]
  simp only [← mul_sub]
  exact abs_sum_moebius_div_sq_mul_le hEsub hK hterm

/-- **Truncating the constants `A` and `B` at `R^{1/8}`.**  For `R ≥ 6561` and `1 ≤ d ≤ R`,
replacing `A Wt` and `B Wt` by their partial sums over `Finset.Icc 1 ⌊R^{1/8}⌋₊` moves the
leading term `g · (A Wt · log (R/d) − 2 · B Wt)` by at most `8 · log R / R^{1/8}`, uniformly
over `0 ≤ g ≤ 1`. -/
private lemma abs_partial_leading_sub_le_log_div_rpow (Wt d : ℕ) {R g : ℝ}
    (hR : (6561 : ℝ) ≤ R) (hd : 0 < d) (hdR : (d : ℝ) ≤ R) (hg : 0 ≤ g) (hg1 : g ≤ 1) :
    |g * (Real.log (R / d) * (∑ e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊, ASummand Wt e) -
          2 * (∑ e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊, BSummand Wt e)) -
        g * (A Wt * Real.log (R / d) - 2 * B Wt)| ≤ 8 * Real.log R / R ^ (1 / 8 : ℝ) := by
  have hRpos : (0 : ℝ) < R := by linarith
  have hdR1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hR8_pos : (0 : ℝ) < R ^ (1 / 8 : ℝ) := by positivity
  set m : ℕ := ⌊R ^ (1 / 8 : ℝ)⌋₊ with hm
  have hR8_ge3 : (3 : ℝ) ≤ R ^ (1 / 8 : ℝ) := by
    have h2 : ((6561 : ℝ)) ^ (1 / 8 : ℝ) = 3 := by
      rw [show (6561 : ℝ) = (3 : ℝ) ^ (8 : ℕ) by norm_num, ← Real.rpow_natCast (3 : ℝ) 8,
        ← Real.rpow_mul (by norm_num)]
      norm_num
    exact h2.symm.trans_le (Real.rpow_le_rpow (by norm_num) hR (by norm_num))
  have hm_ge3 : 3 ≤ m := Nat.le_floor (by push_cast; linarith only [hR8_ge3])
  have hm_pos : 0 < m := by omega
  have hmR : (m : ℝ) ≤ R ^ (1 / 8 : ℝ) := by rw [hm]; exact Nat.floor_le hR8_pos.le
  have hm_half : R ^ (1 / 8 : ℝ) / 2 ≤ (m : ℝ) := by
    have := Nat.sub_one_lt_floor (R ^ (1 / 8 : ℝ))
    rw [hm]; linarith only [this, hR8_ge3]
  have hlogRd_nn : (0 : ℝ) ≤ Real.log (R / d) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by positivity)]; linarith)
  have hlogRd_le : Real.log (R / d) ≤ Real.log R :=
    Real.log_le_log (by positivity) (div_le_self hRpos.le hdR1)
  have hone_over_m : (1 : ℝ) / (m : ℝ) ≤ 2 / R ^ (1 / 8 : ℝ) := by
    rw [div_le_div_iff₀ (by positivity) hR8_pos]
    linarith only [hm_half]
  have hlogm : Real.log (m : ℝ) ≤ (1 / 8) * Real.log R := by
    rw [← Real.log_rpow hRpos]
    exact Real.log_le_log (by exact_mod_cast hm_pos) hmR
  have hlogR1 : (1 : ℝ) ≤ Real.log R := by
    simpa using Real.log_le_log (Real.exp_pos 1)
      (by linarith [Real.exp_one_lt_d9] : rexp 1 ≤ R)
  have hnum_le : Real.log R + 2 * Real.log (m : ℝ) + 2 ≤ 4 * Real.log R := by
    linarith only [hlogm, hlogR1]
  calc |g * (Real.log (R / d) * (∑ e ∈ Finset.Icc 1 m, ASummand Wt e) -
            2 * (∑ e ∈ Finset.Icc 1 m, BSummand Wt e)) -
          g * (A Wt * Real.log (R / d) - 2 * B Wt)| ≤
        (Real.log R + 2 * Real.log (m : ℝ) + 2) / (m : ℝ) :=
      abs_partial_leading_sub_le Wt m hm_ge3 hg hg1 hlogRd_nn hlogRd_le hlogR1
    _ = (Real.log R + 2 * Real.log (m : ℝ) + 2) * (1 / (m : ℝ)) := by ring
    _ ≤ (4 * Real.log R) * (2 / R ^ (1 / 8 : ℝ)) :=
        mul_le_mul hnum_le hone_over_m (by positivity) (by linarith only [hlogR1])
    _ = 8 * Real.log R / R ^ (1 / 8 : ℝ) := by ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **Sub-lemma (main-part evaluation).**  For `e` in the range `1 ≤ e ≤ R^{1/8}`
coprime to `𝒲 = d·(W N)`, the per-`e` term of the `T_decomposition` sum,
`(μe/e²)·(inner w-sum)`, is approximated by the "leading" term
`(μe/e²)·(φ𝒲/𝒲)·(log R − log d − 2 log e)` with error
`|μe/e²|·C·(φ𝒲/𝒲)·(1+loglog(e₀·𝒲))`. -/
theorem slem_T_d_eval_main_part (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in Filter.atTop, ∀ d : ℕ, Squarefree d → Nat.Coprime d (W N) →
      (d : ℝ) ≤ R ^ (1 / 2 : ℝ) → let 𝒲 := d * W N
        |(∑ e ∈ (Finset.Icc 1 ⌊√(R / d)⌋₊).filter
              (fun e : ℕ ↦ e.Coprime (d * W N) ∧ (e : ℝ) ≤ R ^ (1 / 8 : ℝ)),
            (μ e : ℝ) / e ^ 2 *
              (∑ w ∈ Finset.Icc 1 ⌊R / (d * e ^ 2)⌋₊ with w.Coprime (d * W N),
                1 / (w : ℝ))) - (𝒲.totient : ℝ) / 𝒲 * (A 𝒲 * Real.log (R / d) - 2 * B 𝒲)| ≤
          C * ((𝒲.totient : ℝ) / 𝒲) * (Real.log (2 * d) + Real.log (Real.log (W N))) +
            C * Real.log R / R ^ (1 / 8 : ℝ) := by
  obtain ⟨Cinn, hCinn, hinner⟩ := slem_T_d_inner_w_sum δ θ hδθ
  set c0 : ℝ := (1 + Real.log 2) / Real.log 2 + 1 with hc0
  have hc0pos : 0 < c0 := by rw [hc0]; positivity
  refine ⟨max (Cinn * 2 * c0) 8, by positivity, ?_⟩
  set Cm : ℝ := max (Cinn * 2 * c0) 8
  filter_upwards [hinner, R_eventually_ge θ δ hδθ.2.1 256,
    R_eventually_ge θ δ hδθ.2.1 6561, W_eventually_ge_exp1]
    with N hinnerN hR256 hR6561 hWexp
  intro d hd_sf hd_cop hd_le
  simp only
  set 𝒲 := d * W N with h𝒲def
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sf.ne_zero
  have hdR : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
  have hRpos : (0 : ℝ) < R := lt_of_lt_of_le (by norm_num) hR256
  have hR1 : (1 : ℝ) ≤ R := le_trans (by norm_num) hR256
  have h𝒲cast : (𝒲 : ℝ) = (d : ℝ) * (W N : ℝ) := by rw [h𝒲def]; push_cast; ring
  set g : ℝ := (𝒲.totient : ℝ) / 𝒲 with hg
  have hg_nn : (0 : ℝ) ≤ g := by rw [hg]; exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hR8_pos : (0 : ℝ) < R ^ (1 / 8 : ℝ) := by positivity
  have hRR8 : R ^ (1 / 8 : ℝ) ≤ √(R / d) := by
    have hRd_ge : R ^ (1 / 2 : ℝ) ≤ R / d := by
      rw [le_div_iff₀ (by exact_mod_cast hd_pos : (0 : ℝ) < (d : ℝ))]
      calc R ^ (1 / 2 : ℝ) * d ≤ R ^ (1 / 2 : ℝ) * R ^ (1 / 2 : ℝ) :=
            mul_le_mul_of_nonneg_left hd_le (by positivity)
        _ = R := by rw [← Real.rpow_add hRpos]; norm_num
    rw [show R ^ (1 / 8 : ℝ) = √(R ^ (1 / 4 : ℝ)) by
          rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hRpos.le]; norm_num]
    exact Real.sqrt_le_sqrt
      ((Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num)).trans hRd_ge)
  set f : ℕ → ℝ := fun e ↦ (μ e : ℝ) / e ^ 2 *
      (∑ w ∈ Finset.Icc 1 ⌊R / (↑d * ↑e ^ 2)⌋₊ with w.Coprime (d * W N), 1 / (w : ℝ)) with hf
  set S1 : ℝ := ∑ e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊, ASummand 𝒲 e with hS1
  set S2 : ℝ := ∑ e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊, BSummand 𝒲 e with hS2
  set T0 : ℝ := g * (Real.log (R / d) * S1 - 2 * S2) with hT0def
  set MT : ℝ := g * (A 𝒲 * Real.log (R / d) - 2 * B 𝒲) with hMTdef
  set Tsum : ℝ := ∑ e ∈ (Finset.Icc 1 ⌊√(R / d)⌋₊).filter
    (fun e : ℕ ↦ e.Coprime (d * W N) ∧ (e : ℝ) ≤ R ^ (1 / 8 : ℝ)), f e with hTsum
  have hmid : |Tsum - T0| ≤ Cinn * 2 * (g * (1 + Real.log (Real.log (rexp 1 * (𝒲 : ℝ))))) := by
    set K : ℝ := Cinn * g * (1 + Real.log (Real.log (rexp 1 * (𝒲 : ℝ)))) with hK
    have h𝒲one : (1 : ℝ) ≤ (𝒲 : ℝ) := by
      have h1W : (1 : ℝ) ≤ (W N : ℝ) := le_trans (by linarith [Real.exp_one_gt_d9]) hWexp
      rw [h𝒲cast]; nlinarith
    have hK_nn : (0 : ℝ) ≤ K := by
      rw [hK]
      exact mul_nonneg (mul_nonneg hCinn.le hg_nn)
        (by linarith [log_log_exp_one_mul_nonneg h𝒲one])
    have hterm : ∀ e ∈ {e ∈ Finset.Icc 1 ⌊R ^ (1 / 8 : ℝ)⌋₊ |
        Nat.Coprime e (d * W N)},
        |(∑ w ∈ Finset.Icc 1 ⌊R / ((d : ℝ) * (e : ℝ) ^ 2)⌋₊ with Nat.Coprime w (d * W N),
            1 / (w : ℝ)) - g * (Real.log R - Real.log d - 2 * Real.log e)| ≤ K := by
      intro e he
      rw [Finset.mem_filter, Finset.mem_Icc] at he
      obtain ⟨⟨he1, hem⟩, hecop⟩ := he
      have heR8 : (e : ℝ) ≤ R ^ (1 / 8 : ℝ) :=
        le_trans (by exact_mod_cast hem) (Nat.floor_le hR8_pos.le)
      have hinner_e := hinnerN d e hd_sf hd_cop hd_le he1 heR8 hecop
      have heq0 : g * (Real.log R - Real.log d - 2 * Real.log e) =
          (𝒲.totient : ℝ) / 𝒲 * (Real.log R - Real.log ↑d - 2 * Real.log ↑e) := by
        rw [hg]
      have hKeq : K = Cinn * ((𝒲.totient : ℝ) / 𝒲) *
          (1 + Real.log (Real.log (rexp 1 * (𝒲 : ℝ)))) := by
        rw [hK, hg]
      rw [heq0, hKeq]
      exact hinner_e
    calc |Tsum - T0| ≤ 2 * K := by
          simp only [hTsum, hT0def, hS1, hS2, hf, h𝒲def]
          exact abs_sum_moebius_inner_sub_partial_leading_le hRpos hd_pos hRR8 hK_nn hterm
      _ = Cinn * 2 * (g * (1 + Real.log (Real.log (rexp 1 * (𝒲 : ℝ))))) := by
            rw [hK]; ring
  have hloglog : g * (1 + Real.log (Real.log (rexp 1 * (𝒲 : ℝ)))) ≤
      c0 * (g * (Real.log (2 * d) + Real.log (Real.log (W N)))) := by
    have hconv := loglog_conversion d (W N) hd_pos hWexp
    rw [h𝒲cast, mul_comm c0 _, mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hg_nn
    calc 1 + Real.log (Real.log (rexp 1 * ((d : ℝ) * (W N : ℝ))))
        ≤ c0 * (Real.log (2 * d) + Real.log (Real.log (W N))) := hconv
      _ = (Real.log (2 * d) + Real.log (Real.log (W N))) * c0 := by ring
  have hlead : |T0 - MT| ≤ 8 * Real.log R / R ^ (1 / 8 : ℝ) := by
    have hgle1 : g ≤ 1 := by
      rw [hg]; exact div_le_one_of_le₀ (by exact_mod_cast Nat.totient_le 𝒲) (by positivity)
    have hdleR : (d : ℝ) ≤ R := by
      have : R ^ (1 / 2 : ℝ) ≤ R := by
        simpa using Real.rpow_le_rpow_of_exponent_le hR1 (by norm_num : (1 / 2 : ℝ) ≤ 1)
      linarith [hd_le]
    rw [hT0def, hMTdef, hS1, hS2]
    exact abs_partial_leading_sub_le_log_div_rpow 𝒲 d hR6561 hd_pos hdleR hg_nn hgle1
  have htri : |Tsum - MT| ≤ |Tsum - T0| + |T0 - MT| := abs_sub_le _ _ _
  have hloglognn : (0 : ℝ) ≤ g * (Real.log (2 * d) + Real.log (Real.log (W N))) := by
    have hlogW : (1 : ℝ) ≤ Real.log (W N) := by
      simpa using Real.log_le_log (Real.exp_pos 1) hWexp
    exact mul_nonneg hg_nn (by
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (d : ℝ)), Real.log_nonneg hlogW])
  have hlogRnn : (0 : ℝ) ≤ Real.log R / R ^ (1 / 8 : ℝ) :=
    div_nonneg (Real.log_nonneg hR1) (by positivity)
  have hCm1 : Cinn * 2 * c0 ≤ Cm := le_max_left _ _
  have hCm2 : (8 : ℝ) ≤ Cm := le_max_right _ _
  calc |Tsum - MT| ≤ |Tsum - T0| + |T0 - MT| := htri
    _ ≤ Cinn * 2 * (g * (1 + Real.log (Real.log (rexp 1 * (𝒲 : ℝ))))) +
          8 * Real.log R / R ^ (1 / 8 : ℝ) := by
        gcongr
    _ ≤ Cinn * 2 * (c0 * (g * (Real.log (2 * d) + Real.log (Real.log (W N))))) +
          8 * Real.log R / R ^ (1 / 8 : ℝ) := by
        gcongr
    _ = (Cinn * 2 * c0) * (g * (Real.log (2 * d) + Real.log (Real.log (W N)))) +
          8 * (Real.log R / R ^ (1 / 8 : ℝ)) := by ring
    _ ≤ Cm * (g * (Real.log (2 * d) + Real.log (Real.log (W N)))) +
          Cm * (Real.log R / R ^ (1 / 8 : ℝ)) := by
        gcongr
    _ = Cm * g * (Real.log (2 * d) + Real.log (Real.log (W N))) +
          Cm * Real.log R / R ^ (1 / 8 : ℝ) := by ring

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- **Sub-lemma (tail identification).**  The part of the `T_decomposition` sum with
`R^{1/8} < e ≤ √(R/d)` is exactly `doubleSum R (W N) d`, so it is bounded by
`O(log R/R^{1/8})` via `doubleSum_ll_log_div_rpow`.

The only mismatch to reconcile is the inner `w`-filter: `T_decomposition` uses
`w ∈ Icc 1 ⌊R/(d·e²)⌋₊ with w.Coprime`, while `innerSum` additionally imposes
`(w:ℝ) ≤ R/(d·e²)`; these two filters agree because `w ≤ ⌊R/(d·e²)⌋₊ ↔ (w:ℝ) ≤
R/(d·e²)` for `w ≥ 1` (`Nat.le_floor` / `Nat.floor` characterization), so each
`innerSum R (W N) d e` equals the corresponding inner `w`-sum in
`T_decomposition`.
Hence the `e`-filtered subsum over `R^{1/8} < e ≤ √(R/d)` equals `doubleSum`. -/
theorem slem_T_d_eval_tail_part (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in Filter.atTop, ∀ d : ℕ, Squarefree d → Nat.Coprime d (W N) →
      (d : ℝ) ≤ R ^ (1 / 2 : ℝ) →
        |∑ e ∈ (Finset.Icc 1 ⌊√(R / d)⌋₊).filter
              (fun e : ℕ ↦ e.Coprime (d * W N) ∧ ¬ ((e : ℝ) ≤ R ^ (1 / 8 : ℝ))),
            (μ e : ℝ) / e ^ 2 *
              (∑ w ∈ Finset.Icc 1 ⌊R / (d * e ^ 2)⌋₊ with w.Coprime (d * W N),
                1 / (w : ℝ))| ≤ C * Real.log R / R ^ (1 / 8 : ℝ) := by
  obtain ⟨Ct, hCt, hbody⟩ := doubleSum_ll_log_div_rpow
  refine ⟨Ct, hCt, ?_⟩
  have htail := hbody θ δ (by linarith only [hδθ.1, hδθ.2.1]) hδθ.2.2 hδθ.1 hδθ.2.1
  filter_upwards [htail] with N htailN
  intro d hd_sf hd_cop hd_le
  have hEq : (∑ e ∈ (Finset.Icc 1 ⌊√(R / d)⌋₊).filter
        (fun e : ℕ ↦ e.Coprime (d * W N) ∧ ¬ ((e : ℝ) ≤ R ^ (1 / 8 : ℝ))),
        (μ e : ℝ) / e ^ 2 *
          (∑ w ∈ Finset.Icc 1 ⌊R / (d * e ^ 2)⌋₊ with w.Coprime (d * W N), 1 / (w : ℝ))) =
      doubleSum R (W N) d := by
    unfold doubleSum
    refine Finset.sum_congr (Finset.filter_congr fun e he ↦ ?_) fun e _ ↦ ?_
    · rw [Finset.mem_Icc] at he
      have hesqrt : (e : ℝ) ≤ √(R / d) := (Nat.le_floor_iff (Real.sqrt_nonneg _)).mp he.2
      simp only [not_le]
      tauto
    · unfold innerSum
      congr 1
      refine Finset.sum_congr (Finset.filter_congr fun w hw ↦ ?_) fun w _ ↦ rfl
      rw [Finset.mem_Icc] at hw
      have hwle : (w : ℝ) ≤ R / (↑d * ↑e ^ 2) := (Nat.le_floor_iff' (by omega)).mp hw.2
      tauto
  rw [hEq]
  simpa using htailN d hd_sf hd_cop hd_le

open scoped PrimeGaps.sieveTruncation PrimeGaps.sieveModulus in
/-- Statement 1 (`slem_T_d_eval`).  Let `δ, θ : ℝ` with `0 < δ`, `δ < θ/2`, `θ < 1`.
Then there is a constant `C > 0` such that, for all sufficiently large `N`, for every
squarefree `d` coprime to `W N` with `d ≤ R^{1/2}` (real power), writing
`R := R` and `𝒲 := d · (W N)`,
  the real-valued `T` is approximated
by the main term `(φ(𝒲)/𝒲)(A(𝒲)·log(R/d) − 2 B(𝒲))` with a middle error
`O((φ(𝒲)/𝒲)(log(2d) + log log(W N)))` and a tail error `O(log R / R^{1/8})`. -/
@[pg_tag "bg246" "slem_T_d_eval"]
theorem slem_T_d_eval (δ θ : ℝ) (hδθ : 0 < δ ∧ δ < θ / 2 ∧ θ < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N in Filter.atTop, ∀ d : ℕ, Squarefree d → Nat.Coprime d (W N) →
      (d : ℝ) ≤ R ^ (1 / 2 : ℝ) → let 𝒲 := d * W N
        |T R (W N) d - (𝒲.totient : ℝ) / 𝒲 * (A 𝒲 * Real.log (R / d) - 2 * B 𝒲)| ≤
          C * ((𝒲.totient : ℝ) / 𝒲) * (Real.log (2 * d) + Real.log (Real.log (W N))) +
            C * Real.log R / R ^ (1 / 8 : ℝ) := by
  obtain ⟨Cm, hCm, hmain⟩ := slem_T_d_eval_main_part δ θ hδθ
  obtain ⟨Ct, hCt, htail⟩ := slem_T_d_eval_tail_part δ θ hδθ
  refine ⟨Cm + Ct, by positivity, ?_⟩
  filter_upwards [hmain, htail, R_eventually_ge θ δ hδθ.2.1 256,
    W_eventually_ge_exp1] with N hmainN htailN hR256 hWexp
  intro d hd_sf hd_cop hd_le
  simp only at *
  set 𝒲 := d * W N with h𝒲def
  have hmainD := hmainN d hd_sf hd_cop hd_le
  have htailD := htailN d hd_sf hd_cop hd_le
  set f : ℕ → ℝ := fun e ↦ (μ e : ℝ) / e ^ 2 *
      (∑ w ∈ Finset.Icc 1 ⌊R / (↑d * ↑e ^ 2)⌋₊ with w.Coprime (d * W N), 1 / (w : ℝ)) with hf
  set MT : ℝ := (𝒲.totient : ℝ) / 𝒲 * (A 𝒲 * Real.log (R / ↑d) - 2 * B 𝒲)
  set p : ℕ → Prop := fun e : ℕ ↦ (e : ℝ) ≤ R ^ (1 / 8 : ℝ)
  set S : Finset ℕ := (Finset.Icc 1 ⌊√(R / ↑d)⌋₊).filter
    (fun e : ℕ ↦ e.Coprime (d * W N)) with hS
  have hd_pos : 0 < d := Nat.pos_of_ne_zero hd_sf.ne_zero
  have hR1 : (1 : ℝ) ≤ R := le_trans (by norm_num) hR256
  have hTdec : T R (W N) d = ∑ e ∈ S, f e := T_decomposition R hR1 (W N) d hd_pos
  have hsplit : ∑ e ∈ S, f e = (∑ e ∈ S with p e, f e) + (∑ e ∈ S with ¬ p e, f e) :=
    (Finset.sum_filter_add_sum_filter_not S p f).symm
  have hmainEq : (∑ e ∈ S with p e, f e) = ∑ e ∈ (Finset.Icc 1 ⌊√(R / ↑d)⌋₊).filter
        (fun e : ℕ ↦ e.Coprime (d * W N) ∧ (e : ℝ) ≤ R ^ (1 / 8 : ℝ)), f e := by
    rw [hS, Finset.filter_filter]
  have htailEq : (∑ e ∈ S with ¬ p e, f e) = ∑ e ∈ (Finset.Icc 1 ⌊√(R / ↑d)⌋₊).filter
        (fun e : ℕ ↦ e.Coprime (d * W N) ∧ ¬ ((e : ℝ) ≤ R ^ (1 / 8 : ℝ))), f e := by
    rw [hS, Finset.filter_filter]
  rw [hTdec, hsplit, hmainEq, htailEq]
  set mainSum : ℝ := ∑ e ∈ (Finset.Icc 1 ⌊√(R / ↑d)⌋₊).filter
    (fun e : ℕ ↦ e.Coprime (d * W N) ∧ (e : ℝ) ≤ R ^ (1 / 8 : ℝ)), f e
  set tailSum : ℝ := ∑ e ∈ (Finset.Icc 1 ⌊√(R / ↑d)⌋₊).filter
    (fun e : ℕ ↦ e.Coprime (d * W N) ∧ ¬ ((e : ℝ) ≤ R ^ (1 / 8 : ℝ))), f e
  have hL : (0 : ℝ) ≤ (𝒲.totient : ℝ) / 𝒲 * (Real.log (2 * ↑d) + Real.log (Real.log ↑(W N))) := by
    have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd_pos
    have hlogW : (1 : ℝ) ≤ Real.log (W N) := by
      simpa using Real.log_le_log (Real.exp_pos 1) hWexp
    exact mul_nonneg (by positivity) (by
      linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ 2 * (d : ℝ)), Real.log_nonneg hlogW])
  calc |mainSum + tailSum - MT| = |(mainSum - MT) + tailSum| := by congr 1; ring
    _ ≤ |mainSum - MT| + |tailSum| := abs_add_le _ _
    _ ≤ (Cm * ((𝒲.totient : ℝ) / 𝒲) * (Real.log (2 * ↑d) +
      Real.log (Real.log ↑(W N))) + Cm * Real.log R / R ^ (1 / 8 : ℝ)) +
        Ct * Real.log R / R ^ (1 / 8 : ℝ) := add_le_add hmainD htailD
    _ ≤ (Cm + Ct) * ((𝒲.totient : ℝ) / 𝒲) * (Real.log (2 * ↑d) + Real.log (Real.log ↑(W N))) +
          (Cm + Ct) * Real.log R / R ^ (1 / 8 : ℝ) := by
        rw [show (Cm + Ct) * Real.log R / R ^ (1 / 8 : ℝ) =
          Cm * Real.log R / R ^ (1 / 8 : ℝ) + Ct * Real.log R / R ^ (1 / 8 : ℝ) from by ring]
        linarith [mul_nonneg hCt.le hL]

end PrimeGaps
