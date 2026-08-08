/-
Copyright (c) 2026 Axiom Math. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axiom Math
-/
module

public import PrimeGapsTheory.Arithmetic.HAsymptotic.Summability

/-!
# Arithmetic helpers

Bounds for `hfun` and the coprime multiplicativity of `phi`, `ellV` and `tau`.

## Main results

* `boundary_sqrt`
-/

@[expose] public section

open scoped Finset

open scoped ArithmeticFunction.Moebius

namespace PrimeGaps

/-- `hfun n = μ(n)²/φ(n) ∈ [0,1]`. -/
theorem hfun_mem_Icc (n : ℕ) : 0 ≤ hfun n ∧ hfun n ≤ 1 := by
  rw [hfun_apply]
  refine ⟨by positivity, div_le_one_of_le₀ ?_ (by positivity)⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hφ : (1 : ℝ) ≤ (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
    have hμ : (μ n : ℝ) ^ 2 ≤ 1 := by
      rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
      split_ifs <;> norm_num
    linarith

/-- Density kernel decay: `hfun n ≤ 2/√n` for `n ≥ 1`, using
`hfun n ≤ 1/φ(n) ≤ d(n)/n` and the elementary bound `d(n) ≤ 2√n`. -/
theorem hfun_le_sqrt : ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → hfun n ≤ C / √n := by
  refine ⟨2, by norm_num, fun n hn ↦ ?_⟩
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hφpos : (0 : ℝ) < (n.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hτpos : (0 : ℝ) < (#n.divisors : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr (by omega)⟩
  calc hfun n ≤ 1 / (n.totient : ℝ) := by
        rw [hfun_apply]
        gcongr
        rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
        split_ifs <;> norm_num
    _ ≤ (#n.divisors : ℝ) / (n : ℝ) := by
        rw [div_le_div_iff₀ hφpos hnpos, one_mul, mul_comm]
        exact (div_le_iff₀ hτpos).1 (Nat.div_card_le_totient n hn)
    _ ≤ (2 * √n) / n := by
        gcongr
        calc (#n.divisors : ℝ) ≤ 2 * (Nat.sqrt n : ℝ) := by
              exact_mod_cast Nat.card_divisors_le_two_mul_sqrt n
          _ ≤ 2 * √n := by gcongr; exact Real.nat_sqrt_le_real_sqrt
    _ = 2 / √n := by
        rw [div_eq_div_iff hnpos.ne' (Real.sqrt_pos.2 hnpos).ne', mul_assoc,
          Real.mul_self_sqrt hnpos.le]

/-- L1 (boundary_sqrt): strict-vs-nonstrict partial sums differ by `O(1/√x)`. -/
theorem boundary_sqrt : ∃ Cb : ℝ, 0 < Cb ∧ ∀ (m : ℕ) (x : ℝ), 1 ≤ x →
        |partialSumALt m x - PrimeGaps.MaynardOffDiagonal.sumA m x| ≤ Cb / √x := by
  obtain ⟨Cb, hCbpos, hCb⟩ := hfun_le_sqrt
  refine ⟨Cb, hCbpos, fun m x hx ↦ ?_⟩
  set S1 : Finset ℕ :=
    (Finset.range ⌈x⌉₊).filter (fun f : ℕ ↦ 0 < f ∧ (f : ℝ) < x ∧ f.Coprime m) with hS1
  set S2 : Finset ℕ := (Finset.Icc 1 ⌊x⌋₊).filter (fun f : ℕ ↦ f.Coprime m) with hS2
  have hmemS1 : ∀ f, f ∈ S1 ↔ (0 < f ∧ (f : ℝ) < x ∧ f.Coprime m) := fun f ↦ by
    rw [hS1, Finset.mem_filter, Finset.mem_range, and_iff_right_iff_imp]
    exact fun h ↦ Nat.lt_ceil.2 h.2.1
  have hmemS2 : ∀ f, f ∈ S2 ↔ (0 < f ∧ (f : ℝ) ≤ x ∧ f.Coprime m) := fun f ↦ by
    rw [hS2, Finset.mem_filter, Finset.mem_Icc,
      Nat.le_floor_iff (by linarith : (0 : ℝ) ≤ x), and_assoc]
    exact Iff.rfl
  -- every element of `S2 \ S1` sits exactly at the boundary `f = x`
  have key : ∀ f ∈ S2 \ S1, 0 < f ∧ (f : ℝ) = x := fun f hf ↦ by
    rw [Finset.mem_sdiff, hmemS2, hmemS1] at hf
    obtain ⟨⟨h0, hle, hcop⟩, hnot⟩ := hf
    exact ⟨h0, le_antisymm hle (not_lt.1 fun hlt ↦ hnot ⟨h0, hlt, hcop⟩)⟩
  have hdiff : partialSumALt m x - PrimeGaps.MaynardOffDiagonal.sumA m x =
      -(∑ f ∈ S2 \ S1, hfun f) := by
    have hpsA : PrimeGaps.MaynardOffDiagonal.sumA m x = ∑ f ∈ S2, hfun f := by
      simpa only [hS2, hfun_apply] using sumA_eq_mobiusTotientSum m x
    have hsub : S1 ⊆ S2 := fun f hf ↦ by
      obtain ⟨h0, hlt, hcop⟩ := (hmemS1 f).1 hf
      exact (hmemS2 f).2 ⟨h0, hlt.le, hcop⟩
    rw [show partialSumALt m x = ∑ f ∈ S1, hfun f from rfl, hpsA, Finset.sum_sdiff_eq_sub hsub]
    ring
  have hcard : (#(S2 \ S1) : ℝ) ≤ 1 := by
    refine mod_cast Finset.card_le_one.2 fun a ha b hb ↦ ?_
    exact_mod_cast (key a ha).2.trans (key b hb).2.symm
  rw [hdiff, abs_neg, abs_of_nonneg (Finset.sum_nonneg fun f _ ↦ (hfun_mem_Icc f).1)]
  calc ∑ f ∈ S2 \ S1, hfun f ≤ #(S2 \ S1) • (Cb / √x) :=
        Finset.sum_le_card_nsmul _ _ _ fun f hf ↦ by
          rw [← (key f hf).2]; exact hCb f (key f hf).1
    _ ≤ Cb / √x := by
        rw [nsmul_eq_mul]
        exact mul_le_of_le_one_left (div_nonneg hCbpos.le (Real.sqrt_nonneg x)) hcard

/-- L2 (phi_mul_div): coprime multiplicativity of `φ(n)/n`. -/
theorem phi_mul_div {V e : ℕ} (h : V.Coprime e) :
    ((V * e).totient : ℝ) / (V * e) = ((V.totient : ℝ) / V) * ((e.totient : ℝ) / e) := by
  rw [Nat.totient_mul h]
  push_cast
  exact mul_div_mul_comm ..

/-- L3 (`ellV_mul`): coprime additivity of `ellV`. -/
theorem ellV_mul {V e : ℕ} (h : V.Coprime e) : ellV (V * e) = ellV V + ellV e := by
  unfold ellV
  rw [Nat.Coprime.primeFactors_mul h, Finset.sum_union (Nat.Coprime.disjoint_primeFactors h)]

/-- L4 (tau_mul): coprime multiplicativity of divisor count. -/
theorem tau_mul {V e : ℕ} (h : V.Coprime e) :
    (#(V * e).divisors : ℝ) = (#V.divisors : ℝ) * (#e.divisors : ℝ) :=
  mod_cast Nat.Coprime.card_divisors_mul h

/-- L5 (`ellV_le_log`): `ℓ(e) ≤ log e` for `e ≥ 1`. -/
theorem ellV_le_log {e : ℕ} (he : 1 ≤ e) : ellV e ≤ Real.log e := by
  have hp2 : ∀ p ∈ e.primeFactors, (2 : ℝ) ≤ (p : ℝ) := fun p hp ↦ by
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le
  calc ellV e ≤ ∑ p ∈ e.primeFactors, Real.log ↑p := by
        refine Finset.sum_le_sum fun p hp ↦ ?_
        have h2 := hp2 p hp
        rw [div_le_iff₀ (by linarith)]
        nlinarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ (p : ℝ))]
    _ = Real.log (∏ p ∈ e.primeFactors, (p : ℝ)) :=
        (Real.log_prod fun p hp ↦ by have := hp2 p hp; positivity).symm
    _ ≤ Real.log e :=
        Real.log_le_log (Finset.prod_pos fun p hp ↦ by have := hp2 p hp; linarith) <| by
          rw [← Nat.cast_prod]
          exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd e)

/-- L6 (log_2Vz_ge_one): `1 ≤ log(2Vz)` when `1 ≤ V` and `2 ≤ z`. -/
theorem log_2Vz_ge_one {V : ℕ} {z : ℝ} (hV : 1 ≤ V) (hz : 2 ≤ z) : 1 ≤ Real.log (2 * V * z) := by
  have hVR : (1 : ℝ) ≤ (V : ℝ) := by exact_mod_cast hV
  rw [Real.le_log_iff_exp_le (by nlinarith)]
  nlinarith [Real.exp_one_lt_d9]

/-- L7 (bTilde_le_bDefect_abs): `|bTilde e| ≤ |bDefect e|`. -/
theorem bTilde_le_bDefect_abs (S : SieveDatum) (e : ℕ) : |S.bTilde e| ≤ |S.bDefect e| :=
  S.abs_bTilde_le_abs_bDefect e

/-- Crude bound: for `x < 2`, the strict partial sum has at most the `f = 1` term, and
`hfun 1 ≤ 1`. -/
theorem partialSumALt_le_one_of_lt_two (m : ℕ) (x : ℝ) (hx : x < 2) : partialSumALt m x ≤ 1 := by
  have hsub : (Finset.range ⌈x⌉₊).filter (fun f : ℕ ↦ 0 < f ∧ (f : ℝ) < x ∧ f.Coprime m) ⊆ {1} := by
    intro f hf
    obtain ⟨-, hf0, hflt, -⟩ := Finset.mem_filter.mp hf
    have : f < 2 := mod_cast hflt.trans hx
    exact Finset.mem_singleton.2 (by omega)
  calc partialSumALt m x ≤ ∑ f ∈ ({1} : Finset ℕ), hfun f :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun f _ _ ↦ (hfun_mem_Icc f).1
    _ = hfun 1 := Finset.sum_singleton _ _
    _ ≤ 1 := (hfun_mem_Icc 1).2

/-- For `x < 1`, no positive `f` satisfies `(f:ℝ) < x`, so the strict partial sum is `0`. -/
theorem partialSumALt_eq_zero_of_lt_one (m : ℕ) (x : ℝ) (hx : x < 1) : partialSumALt m x = 0 :=
  partialSumALt_eq_zero_of_le_one m x hx.le

/-- The strict partial sum is nonnegative (sum of nonnegative `hfun`). -/
theorem partialSumALt_nonneg (m : ℕ) (x : ℝ) : 0 ≤ partialSumALt m x :=
  Finset.sum_nonneg fun f _ ↦ (hfun_mem_Icc f).1

end PrimeGaps
